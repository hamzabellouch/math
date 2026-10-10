import OAI.Probability.EntangledGames.MixedExposure

namespace OAI

universe u_I u_X u_Y u_R u_m u_n u_E u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

lemma list_suffix_prefix_disjoint {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ) :
    ∀ i ∈ l.drop j, i ∉ (l.take j).reverse := by
  have h : (l.take j ++ l.drop j).Nodup := by simpa using hN
  have hd := (List.nodup_append.mp h).2.2
  intro i hi hi'
  exact hd i (List.mem_reverse.mp hi') i hi rfl

lemma list_fresh_not_suffix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ l.drop (j+1) := by
  have h : (l.drop j).Nodup := hN.drop
  rw [List.drop_eq_getElem_cons hj] at h
  exact (List.nodup_cons.mp h).1

lemma list_fresh_not_prefix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ (l.take j).reverse := by
  apply list_suffix_prefix_disjoint l hN j l[j]
  rw [List.drop_eq_getElem_cons hj]
  exact List.mem_cons_self

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
def chainLeft (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.lefts x₀ (l.drop j) (F r)
def chainRight (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (r : R) : Profile I X Y → E := μ.rights y₀ (l.take j).reverse (H r)

omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_step (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainLeft μ x₀ l F j r = μ.left x₀ l[j] (chainLeft μ x₀ l F (j+1) r) := by
  unfold chainLeft
  rw [List.drop_eq_getElem_cons hj]
  rfl
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_step (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainRight μ y₀ l H (j+1) r = μ.right y₀ l[j] (chainRight μ y₀ l H j r) := by
  unfold chainRight
  rw [List.take_succ_eq_append_getElem hj, List.reverse_append]
  rfl

omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_next_local (μ : Law (X×Y)) (x₀ : X) (l : List I) (hN : l.Nodup)
    (F : R → Profile I X Y → E) (hF : ∀ r i, IgnoresRight (F r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresRight (chainLeft μ x₀ l F (j+1) r) l[j] :=
  lefts_ignoresRight_notMem μ x₀ _ (list_fresh_not_suffix l hN j hj) (hF r _)
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_prev_local (μ : Law (X×Y)) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (H : R → Profile I X Y → E) (hH : ∀ r i, IgnoresLeft (H r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresLeft (chainRight μ y₀ l H j r) l[j] :=
  rights_ignoresLeft_notMem μ y₀ _ (list_fresh_not_prefix l hN j hj) (hH r _)

omit [DecidableEq m] [DecidableEq n] in
lemma chain_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (j : ℕ) :
    (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (chainLeft μ x₀ l F j r z) (chainRight μ y₀ l H j r z))) =
    ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z)) := by
  apply Finset.sum_congr rfl
  intro r _
  apply mixed_pairing μ x₀ y₀ _ _ (list_suffix_prefix_disjoint l hN j) C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
  · exact fun i hi => hθL r i (List.mem_of_mem_drop hi)
  · exact fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi))
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Nonempty R] in
lemma tested_weight_sum_le (ρ : Law Z) (θ : R → Z → ℝ) (hθ1 : ∀ r z, θ r z ≤ 1) :
    (∑ t : R×Z, ρ.weight t.2 * θ t.1 t.2) ≤ Fintype.card R := by
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _r : R, ∑ z, ρ.weight z := by
      apply Finset.sum_le_sum; intro r _
      exact Finset.sum_le_sum (fun z _ => by nlinarith [ρ.nonneg z, hθ1 r z])
    _ = _ := by simp only [ρ.total, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma averaged_potential_left_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z)) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_left_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_left_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma averaged_potential_right_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z))) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z)))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_right_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_right_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma fin_telescope_bound {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U (i+1)-U i) (h0 : -L ≤ U 0) (hN : U N ≤ 0) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U (i+1)-U i) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U N-U 0 := by rw [Fin.sum_univ_eq_sum_range (fun i => U (i+1)-U i), Finset.sum_range_sub]
    _ ≤ L := by linarith

lemma fin_telescope_bound_rev {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U i-U (i+1)) (h0 : U 0 ≤ 0) (hN : -L ≤ U N) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U i-U (i+1)) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U 0-U N := by rw [Fin.sum_univ_eq_sum_range (fun i => U i-U (i+1)), Finset.sum_range_sub']
    _ ≤ L := by linarith
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

abbrev ExposureIndex (l : List I) := Fin (l.length+1) × R × Profile I X Y

def chainLeftFamily (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (F : R → Profile I X Y → Matrix m m ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix m m ℂ :=
  fun t => chainLeft μ x₀ l F t.1 t.2.1 t.2.2

def chainRightFamily (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (H : R → Profile I X Y → Matrix n n ℂ) :
    ExposureIndex (R := R) (X := X) (Y := Y) l → Matrix n n ℂ :=
  fun t => chainRight μ y₀ l H t.1 t.2.1 t.2.2

lemma chain_error_bounds (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    (hFlocal : ∀ r i, IgnoresRight (F r) i) (hHlocal : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    {p : ℝ} (hp : 0 < p)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z))) = p) :
    let A := chainLeftFamily μ x₀ l F
    let B := chainRightFamily μ y₀ l H
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      ((commonMap A (chainLeft μ x₀ l F (j+1) r z)-commonMap A (chainLeft μ x₀ l F j r z))*C*
        (commonMap B (chainRight μ y₀ l H j r z))ᵀ))) ≤ p*Real.log ((Fintype.card R : ℝ)/p) ∧
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      (commonMap A (chainLeft μ x₀ l F (j+1) r z)*C*
        (commonMap B (chainRight μ y₀ l H j r z)-commonMap B (chainRight μ y₀ l H (j+1) r z))ᵀ))) ≤
      p*Real.log ((Fintype.card R : ℝ)/p) := by
  let ρ := pi (fun _ : I => μ)
  let A := chainLeftFamily μ x₀ l F
  let B := chainRightFamily μ y₀ l H
  let f := chainLeft μ x₀ l F
  let h := chainRight μ y₀ l H
  have hfpos : ∀ j r z, (f j r z).PosSemidef :=
    fun j r => lefts_posSemidef μ x₀ _ _ (hF r)
  have hf1 : ∀ j r z, f j r z ≤ 1 := fun j r => lefts_le μ x₀ _ _ (hF1 r)
  have hhpos : ∀ j r z, (h j r z).PosSemidef :=
    fun j r => rights_posSemidef μ y₀ _ _ (hH r)
  have hh1 : ∀ j r z, h j r z ≤ 1 := fun j r => rights_le μ y₀ _ _ (hH1 r)
  have hA : ∀ t, (A t).PosSemidef := fun t => hfpos _ _ _
  have hA1 : ∀ t, A t ≤ 1 := fun t => hf1 _ _ _
  have hB : ∀ t, (B t).PosSemidef := fun t => hhpos _ _ _
  have hB1 : ∀ t, B t ≤ 1 := fun t => hh1 _ _ _
  have hfRange : ∀ j, j ≤ l.length → ∀ r z, f j r z ∈ Set.range A := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  have hhRange : ∀ j, j ≤ l.length → ∀ r z, h j r z ∈ Set.range B := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  let U : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
  let Z : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))
  have hmass (j : ℕ) : (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (h j r z))) = p :=
    (chain_mass μ x₀ y₀ l hN C F H hFlocal hHlocal θ hθL hθR j).trans hm
  have hU (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ U j ∧ U j ≤ 0 :=
    averaged_potential_left_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  have hZ (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ Z j ∧ Z j ≤ 0 :=
    averaged_potential_right_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  constructor
  · apply fin_telescope_bound U _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (by simpa only [neg_mul] using (hU 0).1) (hU _).2
    intro j
    have hs (r : R) := step_left μ x₀ y₀ l[j.val] C A B hA hA1 hB
      (f (j+1) r) (h j r) (hfRange _ (by omega) r)
      (by rw [← chainLeft_step μ x₀ l F j j.isLt]; exact hfRange _ (by omega) r)
      (hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f (j+1) r z)) (h (j+1) r z))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
  · apply fin_telescope_bound_rev Z _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (hZ 0).2 (by simpa only [neg_mul] using (hZ _).1)
    intro j
    have hs (r : R) := step_right μ x₀ y₀ l[j.val] C A B hA hB hB1
      (f (j+1) r) (h j r) (hfRange _ (by omega) r) (hhRange _ (by omega) r)
      (by rw [← chainRight_step μ y₀ l H j j.isLt]; exact hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (f (j+1) r z) (effectEntropy (h (j+1) r z)))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def massAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (q : X×Y) : ℝ :=
  (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
    prob C (F r (Function.update z i q)) (H r (Function.update z i q)))

omit [Fintype n] [Fintype I] [Fintype R] [DecidableEq X] [DecidableEq n] [DecidableEq m] in
lemma right_update_eq (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (H : Profile I X Y → Matrix n n ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ i H (Function.update z i q) =
      (μ.givenFirst y₀ q.1).avg (fun y => H (Function.update z i (q.1,y))) := by
  simp only [right, Function.update_self, updateRight, Function.update_idem]
omit [Fintype m] [Fintype I] [Fintype R] [DecidableEq Y] [DecidableEq n] [DecidableEq m] in
lemma left_update_eq (μ : Law (X×Y)) (x₀ : X) (i : I)
    (F : Profile I X Y → Matrix m m ℂ) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ i F (Function.update z i q) =
      (μ.givenSecond x₀ q.2).avg (fun x => F (Function.update z i (x,q.2))) := by
  simp only [left, Function.update_self, updateLeft, Function.update_idem]

omit [DecidableEq X] [DecidableEq m] [DecidableEq n] in
lemma massAt_right (μ : Law (X×Y)) (y₀ : Y) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hF : ∀ r, IgnoresRight (F r) i) (q : X×Y) :
    massAt μ θ p i C F (fun r => μ.right y₀ i (H r)) q =
      (μ.givenFirst y₀ q.1).avg (fun y => massAt μ θ p i C F H (q.1,y)) := by
  unfold massAt
  rw [show (fun y => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) =
        (fun y => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun y => θ r z*prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) =
      (fun y => θ r z • prob C (F r (Function.update z i (q.1,y))) (H r (Function.update z i (q.1,y)))) from rfl,
    avg_smul]
  dsimp only
  rw [right_update_eq]
  congr 1
  have he (y : Y) : F r (Function.update z i (q.1,y)) = F r (Function.update z i q) := by
    simpa only [updateRight, Function.update_self, Function.update_idem] using hF r (Function.update z i q) y
  simp_rw [he]
  exact (μ.givenFirst y₀ q.1).avg_linear _ (probRight C (F r (Function.update z i q)))

omit [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_left (μ : Law (X×Y)) (x₀ : X) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (hH : ∀ r, IgnoresLeft (H r) i) (q : X×Y) :
    massAt μ θ p i C (fun r => μ.left x₀ i (F r)) H q =
      (μ.givenSecond x₀ q.2).avg (fun x => massAt μ θ p i C F H (x,q.2)) := by
  unfold massAt
  rw [show (fun x => (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) =
        (fun x => (1/p) • ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2))))) from rfl,
    avg_smul, avg_sum]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [avg_comm]
  congr 1; funext z
  rw [show (fun x => θ r z*prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) =
      (fun x => θ r z • prob C (F r (Function.update z i (x,q.2))) (H r (Function.update z i (x,q.2)))) from rfl,
    avg_smul]
  dsimp only
  rw [left_update_eq]
  congr 1
  have he (x : X) : H r (Function.update z i (x,q.2)) = H r (Function.update z i q) := by
    simpa only [updateLeft, Function.update_self, Function.update_idem] using hH r (Function.update z i q) x
  simp_rw [he]
  exact (μ.givenSecond x₀ q.2).avg_linear _ (probLeft C (H r (Function.update z i q)))
end ThresholdParallelRepetition.MixedExposure

end

end OAI
