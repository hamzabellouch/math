import OAI.Dynamics.StandardMap.BridgeExclusions

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def MidpointAffineOn (d : ℝ → ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀s∈U,∀t∈U,s< t → d s ((s+t)/2)=d s t/2 ∧ d ((s+t)/2) t=d s t/2
lemma midpoint_grid_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (a b : ℝ) (hab : a< b) (hm : MidpointAffineOn d (Icc a b))
    (N : ℕ) (hN : 0< N) (i j : ℕ) (hi : i≤ N) (hj : j≤ N) :
    d (a+(i:ℝ)*((b-a)/N)) (a+(j:ℝ)*((b-a)/N))=
      (d a b/(b-a))*|(a+(j:ℝ)*((b-a)/N))-(a+(i:ℝ)*((b-a)/N))| := by
  let h : ℝ := (b-a)/N
  let x : ℕ → ℝ := fun i => a+(i:ℝ)*h
  have hNR : (0:ℝ)< N := by exact_mod_cast hN
  have hp : 0< h := div_pos (sub_pos.mpr hab) hNR
  have hx0 : x 0=a := by simp [x]
  have hxN : x N=b := by dsimp [x,h]; field_simp; ring
  have hdiff (i k : ℕ) : x (i+k)-x i=(k:ℝ)*h := by dsimp [x]; push_cast; ring
  have hmem (i : ℕ) (hi : i≤ N) : x i∈Icc a b := by
    have hib : (i:ℝ)≤ N := by exact_mod_cast hi
    have hh := mul_le_mul_of_nonneg_right hib hp.le
    have hi0 : (0:ℝ)≤ i := Nat.cast_nonneg i
    change a+(N:ℝ)*h=b at hxN
    dsimp [x]
    constructor <;> nlinarith
  have hmid (i : ℕ) : (x i+x (i+2))/2=x (i+1) := by dsimp [x]; push_cast; ring
  have halves (i : ℕ) (hi : i+2≤ N) :
      d (x i) (x (i+1))=d (x i) (x (i+2))/2 ∧
      d (x (i+1)) (x (i+2))=d (x i) (x (i+2))/2 := by
    have hh := hm (x i) (hmem i (by omega)) (x (i+2)) (hmem _ hi)
      (by have hh := hdiff i 2; push_cast at hh; linarith)
    simpa only [hmid] using hh
  let c := d (x 0) (x 1)
  have hedge : ∀i,i< N → d (x i) (x (i+1))=c := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hh := halves i (by omega)
      have he := ih (by omega)
      simpa only [Nat.succ_eq_add_one,show i+1+1=i+2 by omega] using hh.2.trans (hh.1.symm.trans he)
  let w := c/h
  have hw : 0≤ w := div_nonneg (hd.nonneg _ _) hp.le
  have hwhole (i n : ℕ) (hn : i+n≤ N) : d (x i) (x (i+n))=w*(x (i+n)-x i) := by
    have hh := tree_chain_affine hd (fun k => x (i+k)) n w hw
      (fun k hk => by have hh := hdiff (i+k) 1; push_cast at hh; simpa only [Nat.add_assoc] using (show x (i+k)< x (i+k+1) by linarith))
      (fun k hk => by
        rw [←Nat.add_assoc,hedge (i+k) (by omega),hdiff]
        simp only [Nat.cast_one,one_mul]
        dsimp [w]
        rw [div_mul_cancel₀ _ hp.ne'])
      (fun k hk => by
        have hh := (halves (i+k) (by omega)).1
        rw [hedge (i+k) (by omega)] at hh
        rw [←Nat.add_assoc,hdiff]
        push_cast
        have hc : w*h=c := div_mul_cancel₀ _ hp.ne'
        nlinarith)
    simpa only [Nat.add_zero] using hh
  have hwD : w=d a b/(b-a) := by
    have hh := hwhole 0 N (by omega)
    simp only [Nat.zero_add,hx0,hxN] at hh
    exact (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr hh.symm
  change d (x i) (x j)=(d a b/(b-a))*|x j-x i|
  wlog hij : i≤ j generalizing i j
  · rw [hd.symm,abs_sub_comm]
    exact this j i hj hi (le_of_not_ge hij)
  have hh := hwhole i (j-i) (by omega)
  rw [Nat.add_sub_of_le hij,hwD] at hh
  rw [abs_of_nonneg (by
    have hh := mul_le_mul_of_nonneg_right (show (i:ℝ)≤ j by exact_mod_cast hij) hp.le
    dsimp [x]; linarith)]
  exact hh
end StandardMapEntropy

end OAI
