import Mathlib
import OAI.Analysis.MatrixSigning.Realization.RootRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold
import OAI.Analysis.MatrixSigning.Complexity.QueryBits
import OAI.Analysis.MatrixSigning.Complexity.RationalGridBits

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

local notation "X" => NaturalPolynomial.variable

instance poly_wordTail : PolyTime wordTail := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_ratFields : PolyTime ratFields := by unfold ratFields;infer_instance
instance poly_ratNumBinary : PolyTime ratNumBinary := by unfold ratNumBinary;infer_instance
instance poly_unframeNat : PolyTime unframeNat := by unfold unframeNat;apply poly_reindex
instance poly_ratDenBinary : PolyTime ratDenBinary := by unfold ratDenBinary;apply poly_then
instance poly_wordLength : PolyTime wordLength := ⟨⟨3*X+3,fun _ => le_rfl⟩⟩
instance poly_binarySize : PolyTime binarySize := by unfold binarySize;apply poly_congr
instance poly_ratDenSize : PolyTime ratDenSize := by unfold ratDenSize;infer_instance

lemma QParts.abs_le {H : ℕ} {q : ℚ} (h : QParts H q) : |q|≤(2:ℚ)^H :=
  RationalBits.Parts.abs_le h
lemma qparts_of_grid {D H K : ℕ} {q : ℚ} (hD : 0<D) (hg : Grid D q)
    (hd : D≤2^K) (hq : |q|≤(2:ℚ)^H) : QParts (H+K) q := by
  have hden := (hg.den_le hD).trans hd
  have he : |(q.num:ℚ)|=|q| * (q.den:ℚ) := by
    have h := congrArg abs (Rat.num_div_den q)
    rw [abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)] at h
    exact (div_eq_iff (by positivity : (q.den:ℚ)≠0)).mp h
  have hn : (q.num.natAbs:ℚ)≤(2:ℚ)^(H+K) := by
    rw [Nat.cast_natAbs,Int.cast_abs,he,pow_add]
    exact mul_le_mul hq (by exact_mod_cast hden) (by positivity) (by positivity)
  exact ⟨by exact_mod_cast hn,hden.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
lemma grid_mono {D E : ℕ} {q : ℚ} (hg : Grid D q) (hd : D∣E) : Grid E q := hg.trans hd
lemma grid_mid {D : ℕ} {a b : ℚ} (ha : Grid D a) (hb : Grid D b) :
    Grid (D*2) ((a+b)/2) := by
  change ((a+b)/2).den∣D*2
  have h := Rat.mul_den_dvd (a+b) (1/2:ℚ)
  norm_num only [show (1/2:ℚ).den=2 from by norm_num] at h
  simpa only [div_eq_mul_inv,one_div,one_mul] using h.trans (Nat.mul_dvd_mul (ha.add hb) (dvd_refl 2))
lemma abs_mid {a b M : ℚ} (ha : |a|≤M) (hb : |b|≤M) : |(a+b)/2|≤M := by
  rw [abs_div,abs_of_pos (by norm_num : (0:ℚ)<2)]
  have ht := (abs_add_le a b).trans (add_le_add ha hb)
  linarith

lemma root_iterate_invariant (pow : ℕ) (q a b : ℚ) (k : ℕ) (M : ℚ)
    (ha : |a|≤M) (hb : |b|≤M) :
    let z := (rootStep pow)^[k] (q,(a,b))
    z.1=q ∧ Grid (a.den*b.den*2^k) z.2.1 ∧ Grid (a.den*b.den*2^k) z.2.2 ∧
      |z.2.1|≤M ∧ |z.2.2|≤M := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero,id_eq,pow_zero,mul_one]
    exact ⟨True.intro,Nat.dvd_mul_right _ _,Nat.dvd_mul_left _ _,ha,hb⟩
  | succ k ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply']
    let z := (rootStep pow)^[k] (q,(a,b))
    have hd : a.den*b.den*2^(k+1)=(a.den*b.den*2^k)*2 := by rw [pow_succ];ring
    have hg : a.den*b.den*2^k∣a.den*b.den*2^(k+1) := by rw [hd];exact Nat.dvd_mul_right _ _
    have hm := grid_mid ih.2.1 ih.2.2.1
    rw [←hd] at hm
    have ham := abs_mid ih.2.2.2.1 ih.2.2.2.2
    change (rootStep pow z).1=q ∧ _
    dsimp only [rootStep]
    split
    · exact ⟨ih.1,hm,grid_mono ih.2.2.1 hg,ham,ih.2.2.2.2⟩
    · exact ⟨ih.1,grid_mono ih.2.1 hg,hm,ih.2.2.2.1,ham⟩

local instance poly_roots_pow {α : Type*} {encoding : α → Word} {value : α → ℚ}
    (routine : Realizes encoding ratCode value) [PolyTime routine] (exponent : ℕ) :
    PolyTime (routine.pow exponent) := by
  induction exponent with
  | zero => unfold Realizes.pow; infer_instance
  | succ exponent hypothesis =>
      let := hypothesis
      unfold Realizes.pow
      infer_instance

instance poly_rootStep (pow : ℕ) : PolyTime (rootStepRealizes pow) := by
  unfold rootStepRealizes;apply poly_congr
instance size_rootStep (pow : ℕ) : IterateSize (rootStepRealizes pow) := by
  refine ⟨⟨100*X+100,?_⟩⟩
  intro p k
  let L := (rootStateCode p).length
  have hq : (ratCode p.1).length≤L := le_prodCode_left p
  have ha : (ratCode p.2.1).length≤L := (le_prodCode_left p.2).trans (le_prodCode_right p)
  have hb : (ratCode p.2.2).length≤L := (le_prodCode_right p.2).trans (le_prodCode_right p)
  have hpa := (qparts_length p.2.1).mono ha
  have hpb := (qparts_length p.2.2).mono hb
  have hi := root_iterate_invariant pow p.1 p.2.1 p.2.2 k ((2:ℚ)^L) hpa.abs_le hpb.abs_le
  dsimp only at hi
  have hd : p.2.1.den*p.2.2.den*2^k≤2^(2*L+k) := by
    rw [pow_add,show 2*L=L+L by omega,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hpa.2 hpb.2)
  have hD : 0<p.2.1.den*p.2.2.den*2^k := by positivity
  have hla := (qparts_of_grid hD hi.2.1 hd hi.2.2.2.1).length
  have hlb := (qparts_of_grid hD hi.2.2.1 hd hi.2.2.2.2).length
  change (ratCode ((rootStep pow)^[k] p).2.1).length≤_ at hla
  change (ratCode ((rootStep pow)^[k] p).2.2).length≤_ at hlb
  change (rootStateCode ((rootStep pow)^[k] p)).length≤100*(L+k)+100
  simp only [rootStateCode,prodCode_length]
  rw [hi.1]
  omega
instance poly_rootRun (pow : ℕ) : PolyTime (rootRun pow) := by unfold rootRun;infer_instance
instance poly_upperSqrt : PolyTime upperSqrt := by unfold upperSqrt;apply poly_congr
instance poly_approxPsi : PolyTime approxPsi := by unfold approxPsi;apply poly_congr
end CurrentKS.Realization

end OAI
