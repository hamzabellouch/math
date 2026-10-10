import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.SquareNorm
import OAI.Combinatorics.IndependentSets.Reduction.InfluenceSqParamMeasurable
import OAI.Combinatorics.IndependentSets.Reduction.Full

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ κ' τ : Type} [Fintype κ] [Fintype κ']

omit [DecidableEq ι] [∀ index, Fintype (M index)] [Fintype κ] in
lemma auxiliary_joint_measurable (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) :
    Measurable (fun v : (Sigma M → ℝ) × (ι → Circle) => auxiliary p r a t v.1 v.2) := by
  apply Measurable.of_eval
  intro k
  exact ((measurable_pi_apply (a (r k))).comp measurable_snd).add
    ((measurable_pi_apply k).comp ((phase_measurable p t).comp measurable_fst))

omit [Fintype κ] [Fintype κ'] in
theorem deleted_zero_from_junta (i j : ι) (p : ∀ j, κ → M j)
    (p' : ∀ j : {j : ι // j ≠ i}, κ' → M j.val) (e : κ → κ')
    (hp : ∀ j k, p j.val k = p' j (e k))
    (q : ∀ j, M j → τ) (r : κ → τ) (hq : ∀ j k, q j (p j k) = r k)
    (a : τ → ι) (t : ι → ℝ) (hi : t i = 0) (hj : t j = 1)
    (F : (κ → Circle) → ℝ) (F' : (κ' → Circle) → ℝ)
    (hFm : Measurable F) (hF'm : Measurable F')
    (hFb : ∀ x, |F x| ≤ 1) (hF'b : ∀ x, |F' x| ≤ 1)
    {c γ : ℝ} (hc : 0 ≤ c) (hγ : c < γ)
    (hcompat : ∀ y, |F (y ∘ e)-F' y| ≤ c)
    (S : Finset (Sigma fun k : {k : ι // k ≠ i} => M k.val))
    (halign : ∀ d ∈ S, d.1.val = j → a (q d.1.val d.2) ≠ i)
    (herr : (∫ θ,
      (F' (phase p' (fun k => t k.val) θ) -
        average rotationLaw S (fun φ => F' (phase p' (fun k => t k.val) φ)) θ)^2
      ∂Measure.pi (fun _ : Sigma (fun k : {k : ι // k ≠ i} => M k.val) => rotationLaw)) < γ^2) :
    (∫ θ, influenceSq volume i (fun z => F (auxiliary p r a t θ z))
      ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < (2*γ)^2 := by
  let h : (Sigma (fun k : {k : ι // k ≠ i} => M k.val) → ℝ) → ℝ :=
    fun θ => F' (phase p' (fun k => t k.val) θ)
  let g := average rotationLaw S h
  let R := restrictRotations (M:=M) i
  have hR := restriction_preserving rotationLaw (eraseCoord (M:=M) i) (eraseCoord_injective i)
  have hhm : Measurable h := hF'm.comp (phase_measurable p' _)
  have hgm : Measurable g := average_measurable rotationLaw S hhm
  have hhb : ∀ θ, |h θ| ≤ 1 := fun θ => hF'b _
  have hgb : ∀ θ, |g θ| ≤ 1 := average_bound rotationLaw S hhb
  have he : (∫ θ, (h (R θ)-g (R θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2 := by
    have htransfer := integral_preserving hR ((hhm.sub hgm).pow_const 2).aestronglyMeasurable
    change (∫ θ, (h (R θ)-g (R θ))^2 ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
      (∫ θ, (h θ-g θ)^2 ∂Measure.pi (fun _ : Sigma (fun k : {k : ι // k ≠ i} => M k.val) => rotationLaw)) at htransfer
    rw [htransfer]
    exact herr
  apply zero_influence_bound q a j i (S.image (eraseCoord i)) (h ∘ R) (g ∘ R)
    (fun v => F (auxiliary p r a t v.1 v.2))
    (hhm.comp hR.measurable) (hgm.comp hR.measurable)
    (hFm.comp (auxiliary_joint_measurable p r a t))
    (fun θ => hhb _) (fun θ => hgb _) (fun v => hFb _)
    ?_ ?_ hc hγ ?_ he
  · intro x y hxy
    apply average_depends
    intro d hd
    exact hxy (eraseCoord i d) (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
  · intro d hd hdj
    obtain ⟨d',hd',rfl⟩ := Finset.mem_image.mp hd
    exact halign d' hd' hdj
  · intro θ z
    dsimp only [Function.comp_def, h, R]
    rw [deleted_auxiliary i j p p' e hp q r hq a t hi hj θ z]
    exact hcompat _
end LargeIndependentSets.PhaseTest

namespace LargeIndependentSets.Coefficient
open scoped Classical
noncomputable def value {m : ℕ} (k : Fin (m+1)) : ℝ := k.val / (m:ℝ)
lemma value_nonneg {m : ℕ} (k : Fin (m+1)) : 0 ≤ value k := by unfold value; positivity
lemma value_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : value k ≤ 1 := by
  rw [value, div_le_one (by exact_mod_cast hm)]
  exact_mod_cast (show k.val ≤ m by omega)
lemma value_abs_le_one {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) : |value k| ≤ 1 := by
  rw [abs_of_nonneg (value_nonneg k)]; exact value_le_one hm k
lemma value_zero {m : ℕ} (k : Fin (m+1)) (hk : k.val=0) : value k=0 := by simp [value,hk]
lemma value_full {m : ℕ} (hm : 0 < m) (k : Fin (m+1)) (hk : k.val=m) : value k=1 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simpa only [value,hk] using div_self hmR
lemma value_lower {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (i : ι) (t : ι → Fin (m+1)) (ht : 0 < (t i).val) :
    |value (t i)-value (lower i t i)| = 1/(m:ℝ) := by
  have hcast : (((t i).val-1 : ℕ):ℝ) = (t i).val-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  simp only [value, lower, Function.update_self, hcast]
  rw [show ((t i).val : ℝ)/(m:ℝ)-((t i).val-1)/(m:ℝ) = 1/(m:ℝ) by ring,
    abs_of_nonneg (by positivity : 0 ≤ 1/(m:ℝ))]
end LargeIndependentSets.Coefficient

namespace LargeIndependentSets.PhaseTest

section
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal

theorem subchain_juntas (L : ℝ≥0) (s : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ s → ∀ (M : ι → Type) [∀ j, Fintype (M j)],
      ∀ (κ : Type) [Fintype κ], ∀ (p : ∀ j, κ → M j)
      (F : (κ → Circle) → ℝ), LipschitzWith L F → (∀ x, |F x| ≤ 1) →
      ∀ m : ℕ, 0 < m → ∃ S : (ι → Fin (m+1)) → Finset (Sigma M),
        (∀ t, (S t).card ≤ J ∧
          (∫ θ, (F (phase p (fun j => Coefficient.value (t j)) θ) -
            average rotationLaw (S t) (fun φ => F (phase p (fun j => Coefficient.value (t j)) φ)) θ)^2
              ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2) ∧
        (Finset.univ.biUnion S).card ≤ J*(m+1)^s := by
  obtain ⟨J,hJ,HJ⟩ := arbitrary_real_junta (L*s) (sq_pos_of_pos hγ)
  refine ⟨J,hJ,?_⟩
  intro ι _ _ hs M _ κ _ p F hF hb m hm
  have hrot : rotationLaw = BooleanJunta.unitLaw := by
    simp only [rotationLaw, BooleanJunta.unitLaw, restrict_Ico_eq_restrict_Icc]
  have hchoice (t : ι → Fin (m+1)) : ∃ S : Finset (Sigma M), S.card ≤ J ∧
      (∫ θ, (F (phase p (fun j => Coefficient.value (t j)) θ)-
        average rotationLaw S (fun φ => F (phase p (fun j => Coefficient.value (t j)) φ)) θ)^2
          ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < γ^2 := by
    have hphase := phase_lipschitz p (fun j => Coefficient.value (t j))
      (fun j => Coefficient.value_abs_le_one hm _)
    have hprod : L*(Fintype.card ι : ℝ≥0) ≤ L*s := mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by positivity : (0 : ℝ≥0) ≤ L)
    have hf := (hF.comp hphase).weaken hprod
    simpa only [hrot, Function.comp_def] using HJ (Sigma M) _ hf (fun θ => hb _)
  choose S hS using hchoice
  refine ⟨S,hS,?_⟩
  calc
    _ ≤ ∑ t : ι → Fin (m+1), (S t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t : ι → Fin (m+1), J := Finset.sum_le_sum (fun t _ => (hS t).1)
    _ = (m+1)^Fintype.card ι * J := by simp
    _ ≤ (m+1)^s * J := Nat.mul_le_mul_right J (Nat.pow_le_pow_right (by omega) hs)
    _ = _ := Nat.mul_comm _ _

lemma terminal_list_card {ι τ : Type*} [Fintype ι] [DecidableEq τ]
    {M : ι → Type*} [∀ j, Fintype (M j)] {m s J : ℕ}
    (S : (ι → Fin (m+1)) → Finset (Sigma M)) (q : ∀ j, M j → τ)
    (hS : (Finset.univ.biUnion S).card ≤ J*(m+1)^s) :
    ((Finset.univ.biUnion S).image (fun c => q c.1 c.2)).card ≤ J*(m+1)^s :=
  Finset.card_image_le.trans hS
end

open MeasureTheory Set ProductAveraging Coefficient
open scoped BigOperators Classical NNReal

lemma rotations_bounded_ae {C : Type*} [Fintype C] :
    ∀ᵐ θ ∂Measure.pi (fun _ : C => rotationLaw), ∀ c, |θ c| ≤ 1 := by
  have hrs : ∀ᵐ y ∂rotationLaw, y ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [ae_all_iff]
  intro c
  have hp := measurePreserving_eval (fun _ : C => rotationLaw) c
  filter_upwards [hp.quasiMeasurePreserving.ae hrs] with θ hθ
  rw [abs_of_nonneg hθ.1]
  exact hθ.2.le

theorem actual_coefficient_mean_square (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (s m : ℕ) (hm : 0 < m) (ρ γ c : ℝ),
    0 ≤ ρ → 0 ≤ c → c < γ →
    (L:ℝ)/m < β/2 →
    (1-levelMass m ρ ⟨m,by omega⟩)^s < ε →
    ρ*K < ε → (s:ℝ)*(2*γ)^2/β^2 < ε →
    ∀ (M : Fin s → Type) [∀ j, Fintype (M j)]
      (κ τ : Type) [Fintype κ],
    ∀ (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ),
    (∀ j k, q j (p j k) = r k) →
    ∀ (F : (κ → Circle) → ℝ), LipschitzWith L F →
    (∀ x, |F x| ≤ 1) →
    (∀ x, F (fun k => x k + ((1/2:ℝ):Circle)) = -F x) →
    ∀ (κ' : Fin s → Type) [∀ i, Fintype (κ' i)]
      (p' : ∀ i, ∀ j : {j : Fin s // j ≠ i}, κ' i → M j.val)
      (e : ∀ i, κ → κ' i),
    (∀ i j k, p j.val k = p' i j (e i k)) →
    ∀ (F' : ∀ i, (κ' i → Circle) → ℝ),
    (∀ i, Measurable (F' i)) → (∀ i x, |F' i x| ≤ 1) →
    (∀ i y, |F (y ∘ e i)-F' i y| ≤ c) →
    ∀ (S : ∀ i, ({j : Fin s // j ≠ i} → Fin (m+1)) →
      Finset (Sigma fun j : {j : Fin s // j ≠ i} => M j.val)),
    (∀ i t, (∫ θ,
      (F' i (phase (p' i) (fun j => value (t j)) θ) -
        average rotationLaw (S i t) (fun φ => F' i (phase (p' i) (fun j => value (t j)) φ)) θ)^2
      ∂Measure.pi (fun _ : Sigma (fun j : {j : Fin s // j ≠ i} => M j.val) => rotationLaw)) < γ^2) →
    ∀ (a : τ → Fin s),
    (∀ i t d, d ∈ S i t → a (q d.1.val d.2) ≠ i) →
    (∑ t : Fin s → Fin (m+1), mass m ρ t *
      ∫ θ, ∫ z, (F (auxiliary p r a (fun j => value (t j)) θ z))^2
        ∂(volume : Measure (Fin s → Circle))
        ∂Measure.pi (fun _ : Sigma M => rotationLaw)) < 4*ε := by
  obtain ⟨β,hβ,K,hK,HT⟩ := torus_influences L hε
  refine ⟨β,hβ,K,hK,?_⟩
  intro s m hm ρ γ c hρ hc hcγ hstep hrare hpos hzero
    M _ κ τ _ p q r hq F hF hb hodd κ' _ p' e hp F' hF'm hF'b hcompat S hjunta a halign
  let H (t : Fin s → Fin (m+1)) (θ : Sigma M → ℝ) (z : Fin s → Circle) :=
    F (auxiliary p r a (fun j => value (t j)) θ z)
  let X (t : Fin s → Fin (m+1)) (θ : Sigma M → ℝ) := ∫ z, (H t θ z)^2
  let D (t : Fin s → Fin (m+1)) (θ : Sigma M → ℝ) (i : Fin s) :=
    influenceNorm volume i (H t θ)
  have hHlip (t : Fin s → Fin (m+1)) (θ : Sigma M → ℝ) : LipschitzWith L (H t θ) := by
    simpa only [H, Function.comp_def, mul_one] using hF.comp (auxiliary_lipschitz p r a (fun j => value (t j)) θ)
  have hHm (t : Fin s → Fin (m+1)) : Measurable (fun v : (Sigma M → ℝ) × (Fin s → Circle) => H t v.1 v.2) :=
    hF.continuous.measurable.comp (auxiliary_joint_measurable p r a _)
  have hXB (t : Fin s → Fin (m+1)) (θ : Sigma M → ℝ) : 0 ≤ X t θ ∧ X t θ ≤ 1 := by
    constructor
    · exact integral_nonneg (fun z => sq_nonneg _)
    · calc
        _ ≤ ∫ _ : Fin s → Circle, (1:ℝ) :=
          integral_mono (bounded_sq_integrable (hHlip t θ).continuous.measurable (fun z => hb _))
            (integrable_const _) (fun z => by
              have hh : |H t θ z| ≤ 1 := hb _
              nlinarith [sq_abs (H t θ z), abs_nonneg (H t θ z)])
        _ = 1 := by simp
  apply coefficient_mean_square_ae (Measure.pi (fun _ : Sigma M => rotationLaw)) hρ hβ (hc.trans_lt hcγ) hε
    (by simpa using hrare) hpos (by simpa using hzero) X D
  · intro t
    exact ((hHm t).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  · exact hXB
  · intro t i
    exact (influenceSq_param_measurable volume i (hHm t)).sqrt
  · intro t θ i
    dsimp only [D, influenceNorm]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by
      simpa using influenceSq_le_bound volume i (hHlip t θ).continuous.measurable (fun z => hb (auxiliary p r a (fun j => value (t j)) θ z))⟩
  · intro t θ hx
    exact (HT s (H t θ) (hHlip t θ) (fun z => hb _)).1
      ⟨auxiliary_mean_zero p r a _ θ F hF.continuous.measurable hodd,hx⟩
  · filter_upwards [rotations_bounded_ae (C:=Sigma M)] with θ hθ
    intro t i hti
    have h := auxiliary_influence_step p r a (fun j => value (t j))
      (fun j => value (lower i t j)) i
      (fun j hji => by simp [lower, hji]) θ hθ
      (by positivity : 0 ≤ 1/(m:ℝ)) (le_of_eq (value_lower hm i t hti)) F hF hb
    exact h.trans_lt (by simpa [div_eq_mul_inv] using hstep)
  · intro t θ
    exact_mod_cast (HT s (H t θ) (hHlip t θ) (fun z => hb _)).2
  · intro t i ht hi
    obtain ⟨j,hj⟩ := ht
    have hz := deleted_zero_from_junta i j p (p' i) (e i) (hp i) q r hq a
      (fun k => value (t k)) (value_zero _ hi) (value_full hm _ hj)
      F (F' i) hF.continuous.measurable (hF'm i) hb (hF'b i) hc hcγ (hcompat i)
      (S i (fun k => t k.val)) (fun d hd _ => halign i _ d hd) (hjunta i (fun k => t k.val))
    simpa only [D, influenceNorm, Real.sq_sqrt (influenceSq_nonneg _ _ _)] using hz
end LargeIndependentSets.PhaseTest

end OAI
