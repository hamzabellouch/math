import OAI.Combinatorics.MatchingPSD.DominationDecoder

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

noncomputable def cutValue (b : Bool) (x : Point) : ℝ := x 0+x (if b then 2 else 1)-1

lemma cell_trace_value {s q r : ℕ}
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (y : Fin q → Bool) (i : Fin q) (x : Point)
    (hx : ∃ M : Pairing (TripleVertices s), crossVector threeColor M=x) :
    (Q y*cellMatrix i B x).trace = cutValue (y i) x := by
  have : Nonempty (Pairing (Fin s × Bool)) := ⟨standardPairing⟩
  rw [trace_cellMatrix]
  apply cellAverage_const i _ x _ hx
  intro M hM N
  rw [hpair, extendLocal_cut, hM]
  rfl

lemma cutValue_p (b : Bool) : cutValue b (origin+dirP) = 0 := by
  cases b <;> norm_num [cutValue, origin, dirP, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_star (b : Bool) : cutValue b (origin+dirStar) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirStar, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_bit (b : Bool) : cutValue b (if b then origin+dirB else origin+dirA) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirA, dirB, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

lemma cutValue_grid {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (g : GridIndex d) (b : Bool) :
    cutValue b (scaledNode L g) ≤ 2*(d:ℝ)*L := by
  have hk (a : Fin 3) : (g a : ℝ) ≤ (d:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (g a).isLt)
  have h0 := mul_le_mul_of_nonneg_left (hk 0) hL
  have h1 := mul_le_mul_of_nonneg_left (hk 1) hL
  have h2 := mul_le_mul_of_nonneg_left (hk 2) hL
  cases b <;> norm_num [cutValue, scaledNode, origin, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> nlinarith

lemma origin_star_eq : origin+dirStar = (![3,0,0] : Point) := by
  ext a
  fin_cases a <;> norm_num [origin, dirStar]

lemma weightMass_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    weightMass d L ≤ c/L^2 := by
  obtain ⟨c,hc,hbound⟩ := weights_bound d
  refine ⟨(Fintype.card (GridIndex d) : ℝ)*c, mul_pos (by positivity) hc, ?_⟩
  intro L hL
  have he := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hbound L hL g)
  simpa only [weightMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc] using he

lemma cell_decoder {s q l r d : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q) (hsl : 2*l*d ≤ s)
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hB : ∀ M, (B M).PosSemidef)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (P : Fin q → Fin r → Fin r → Point → ℝ)
    (hP : ∀ i u v, P i u v ∈ lowDegree coord d)
    {η m δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hl : 0 < l)
    (hm : ∀ y, (Q y).trace ≤ m)
    (happrox : ∀ i u v t, |cellMatrix i B (samplePoint d (2*l) t) u v-
      P i u v (samplePoint d (2*l) t)| ≤ η)
    (hε : 0 ≤ (q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ r := by
  let L : ℝ := 2*l
  have hL : 0 < L := by dsimp [L]; positivity
  let C := fun i => cellMatrix i B
  have hC (i : Fin q) (x : Point) : (C i x).PosSemidef := cellMatrix_psd i B hB x
  have hsamp (y : Fin q → Bool) (i : Fin q) (t : SampleIndex d) :
      (Q y*C i (samplePoint d L t)).trace = cutValue (y i) (samplePoint d L t) :=
    cell_trace_value Q B hpair y i _ (sample_witness hs hsl t)
  have hfive (y : Fin q → Bool) (i : Fin q) (j : Fin 5) :
      (Q y*C i (specialPoint j)).trace = cutValue (y i) (specialPoint j) := hsamp y i (.inl j)
  have hp (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirP)).trace=0 :=
    (hfive y i 1).trans (cutValue_p _)
  have hstar (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirStar)).trace=2 :=
    (hfive y i 2).trans (cutValue_star _)
  have hgrid (y : Fin q → Bool) (i : Fin q) (g : GridIndex d) :
      (Q y*C i (scaledNode L g)).trace ≤ 2*(d:ℝ)*L :=
    (hsamp y i (.inr g)).le.trans (cutValue_grid hL.le g (y i))
  have hEex (i : Fin q) := interpolation_matrix_domination d (C i) (hC i) (P i) (hP i)
    hL.ne' hη (fun j u v => happrox i u v (.inl j)) (fun g u v => happrox i u v (.inr g))
  choose E hE hdom hEb using hEex
  let i₀ : Fin q := ⟨0,by omega⟩
  let S := C i₀ (origin+dirStar)
  have hcommon (i : Fin q) : C i (origin+dirStar)=S := by
    dsimp only [S,C]
    rw [origin_star_eq]
    exact cellMatrix_star i i₀ B 3
  let T := fun i (b : Bool) => if b then C i (origin+dirB) else C i (origin+dirA)
  have hT (i : Fin q) (b : Bool) : (T i b).PosSemidef := by
    cases b <;> exact hC i _
  have hTdom (i : Fin q) : T i false+T i true ≤ S+(2:ℝ) • C i (origin+dirP)+E i := by
    change C i (origin+dirA)+C i (origin+dirB) ≤ S+(2:ℝ) • C i (origin+dirP)+E i
    rw [← hcommon i]
    exact hdom i
  have hbit (y : Fin q → Bool) (i : Fin q) : (Q y*T i (y i)).trace=2 := by
    cases hy : y i
    · exact (hfive y i 3).trans (by rw [hy]; exact cutValue_bit false)
    · exact (hfive y i 4).trans (by rw [hy]; exact cutValue_bit true)
  have he (y : Fin q → Bool) (i : Fin q) : (Q y*E i).trace ≤
      weightMass d L*(2*(d:ℝ)*L)+(r:ℝ)*(6+weightMass d L)*η*m := by
    simpa only [Fintype.card_fin] using hEb i (Q y) m (2*(d:ℝ)*L) (hm y) (hgrid y i)
  simpa only [Fintype.card_fin] using domination_decoder Q T (fun i => C i (origin+dirP)) E S hQ hT
    (fun i => hC i _) hE (hC i₀ _) hTdom hp (fun y => hstar y i₀) hbit hδ hm he hε hsmall

end MatchingInterpolation

end OAI
