import OAI.NumberTheory.TotientAsymptotic.NormalRemainderLayer
import OAI.NumberTheory.TotientAsymptotic.NormalDiscardDecay

namespace OAI

/-! Sum every non-head normality failure, retaining all basic witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonnegative_sum_biUnion_le {α β : Type*} (I : Finset α) (S : α → Finset β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ I.biUnion S, f b) ≤ ∑ a ∈ I, ∑ b ∈ S a, f b := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁ := S a) (s₂ := I.biUnion S) (f := f)
    have hn : 0 ≤ ∑ b ∈ S a ∩ I.biUnion S, f b := Finset.sum_nonneg (fun b _ => hf b)
    linarith

def nonNormalInternalRemainders (x : ℝ) (H : ℕ) : Finset (RemainderDatum (L x H)) :=
  (Finset.Icc 0 (R x H)).biUnion (fun i =>
    (Finset.Icc (max 1 i) (L x H)).biUnion (nonNormalRemainders x H i))

lemma reverse_geometric_sum {M H : ℕ} (hH : H ≤ M) :
    (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) ≤ polynomialGeometricTail 0 rho H := by
  let T := (Finset.Icc 0 (M-H)).image (fun i => M-i-H)
  have hi : Set.InjOn (fun i => M-i-H) (↑(Finset.Icc 0 (M-H)) : Set ℕ) := by
    intro i hi j hj he
    have h1 := Finset.mem_Icc.mp hi
    have h2 := Finset.mem_Icc.mp hj
    change M-i-H=M-j-H at he
    omega
  have he : (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) = ∑ n ∈ T, rho^(H+n) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have := Finset.mem_Icc.mp hi
    omega
  rw [he]
  have hs : Summable (fun n : ℕ => rho^(H+n)) :=
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).comp_injective
      (by intro n m hh; omega)
  simpa only [polynomialGeometricTail,pow_zero,one_mul] using
    hs.sum_le_tsum T (fun n _ => (pow_pos rho_pos _).le)

/-- This includes all positive prime coordinates for every retained normality
scale, a larger family than the manuscript's short normality window. -/
theorem normal_internal_reciprocal_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) (hford : FordLemma26Input) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        (∑ η ∈ nonNormalInternalRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨C,D,hC,hD,hlayer⟩ := normal_remainder_layer_mass hbox hren hmertens hford
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (normal_discard_geometric hC hD)
  filter_upwards [hlayer,ford_band_polynomial_lower 12,eventually_ge_atTop H₀,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hL hpoly hH0 hH hP
  filter_upwards [hL,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hl hp hlog hHm hB
  let W : ℝ := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by positivity)
  have hG : 0 ≤ G x (m x) := (G_pos hB _).le
  have hiBound (i : ℕ) (hi : i ∈ Finset.Icc 0 (R x H)) :
      (∑ η ∈ (Finset.Icc (max 1 i) (L x H)).biUnion (nonNormalRemainders x H i),
        remainderReciprocalWeight η) ≤ W*G x (m x)*rho^(m x-i) := by
    have hiR := (Finset.mem_Icc.mp hi).2
    have him : i < m x := by unfold R at hiR; omega
    have hHi : H ≤ m x-i := by unfold R at hiR; omega
    let h := m x-i
    let b := fordBandScale x i
    let A := C*(2*b+2)^6*Real.exp (-(b^(1/3 : ℝ))/6)*(D*(2*b+2))^(L x H-(i-1)-1)
    have hb0 : 0 ≤ b := (pow_nonneg (Nat.cast_nonneg (m x-i)) 12).trans (hp i him hHi)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hk := hH₀ h (hH0.trans hHi) b (hp i him hHi) (hlog i him)
      (L x H-(i-1)-1) (by dsimp [h]; unfold L; omega)
    have hk' : (h : ℝ)^2*A ≤ rho^h := by simpa only [A,mul_assoc] using hk
    have hc : ((Finset.Icc (max 1 i) (L x H)).card : ℝ) ≤ (h : ℝ)^2 := by
      have hcn : (Finset.Icc (max 1 i) (L x H)).card ≤ h := by
        simp only [Nat.card_Icc]
        dsimp [h]
        unfold L
        omega
      have hh : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by dsimp [h]; omega)
      have hcR : ((Finset.Icc (max 1 i) (L x H)).card : ℝ) ≤ h := by exact_mod_cast hcn
      nlinarith
    calc
      _ ≤ ∑ j ∈ Finset.Icc (max 1 i) (L x H),
          ∑ η ∈ nonNormalRemainders x H i j, remainderReciprocalWeight η :=
        nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
      _ ≤ ∑ _j ∈ Finset.Icc (max 1 i) (L x H), W*G x (m x)*A := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj1,hjL⟩ := Finset.mem_Icc.mp hj
        have he := hl i j hiR ((le_max_left 1 i).trans hj1) ((le_max_right 1 i).trans hj1) hjL
        simpa only [W,A,b,mul_assoc] using he
      _ = W*G x (m x)*(((Finset.Icc (max 1 i) (L x H)).card : ℝ)*A) := by simp; ring
      _ ≤ W*G x (m x)*((h : ℝ)^2*A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hA) (mul_nonneg hW hG)
      _ ≤ _ := mul_le_mul_of_nonneg_left hk' (mul_nonneg hW hG)
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  calc
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H),
        ∑ η ∈ (Finset.Icc (max 1 i) (L x H)).biUnion (nonNormalRemainders x H i), remainderReciprocalWeight η :=
      nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H), W*G x (m x)*rho^(m x-i) := Finset.sum_le_sum hiBound
    _ = W*G x (m x)*(∑ i ∈ Finset.Icc 0 (R x H), rho^(m x-i)) := by rw [Finset.mul_sum]
    _ ≤ (E*Real.exp ((4*(lam/rho))*cofactorScale H))*G x (m x)*polynomialGeometricTail 0 rho H := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hw hG
      · exact reverse_geometric_sum hHm
      · exact Finset.sum_nonneg (fun _ _ => (pow_pos rho_pos _).le)
      · positivity
    _ = _ := by dsimp [ε]; ring

end TotientAsymptotic

end

end OAI
