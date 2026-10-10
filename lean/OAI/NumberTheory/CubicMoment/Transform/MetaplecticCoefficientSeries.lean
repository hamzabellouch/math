import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCoefficientDecay

namespace OAI

/-! Summing the separated arithmetic majorant from the actual Voronoi
support. The two free norm series and the ramified geometric series
converge, while the squarefree supported factor is a divisor of the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_divisor_weight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro r hr
  calc
    _ ≤ ∑ _h ∈ metaplecticPrimaryDivisors r, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (one_le_norm (primary_ne_zero (mem_primaryElementBall.mp (Finset.mem_filter.mp hh).1).1))
        (by linarith)
    _ = ((metaplecticPrimaryDivisors r).card:ℝ) := by simp
    _ ≤ C*norm r^ε := hdiv (primaryElementBall (norm r))
      (fun _ hh => (mem_primaryElementBall.mp hh).1) r (primary_ne_zero hr)

abbrev MetaplecticCoefficientCode (r : Eisenstein) :=
  ℕ × (Eisensteinˣ × ((metaplecticPrimaryDivisors r) × (PrimaryArgument × PrimaryArgument)))

def metaplecticCodeWeight (r : Eisenstein) (σ : ℝ) (z : MetaplecticCoefficientCode r) : ℝ :=
  metaplecticRamifiedRatio σ^z.1 *
    (1*(norm z.2.2.1.val^(-σ)*
      (norm z.2.2.2.1^(-3/2-3*σ)*norm z.2.2.2.2^(-1-σ))))

lemma metaplecticCodeWeight_nonneg (r : Eisenstein) (σ : ℝ)
    (z : MetaplecticCoefficientCode r) : 0 ≤ metaplecticCodeWeight r σ z := by
  unfold metaplecticCodeWeight metaplecticRamifiedRatio
  exact mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
    (mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))))

private lemma metaplectic_product_hasSum {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {A B : ℝ} (hf : HasSum f A) (hg : HasSum g B)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    HasSum (fun z : α × β => f z.1*g z.2) (A*B) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

lemma metaplecticCodeWeight_hasSum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (metaplecticCodeWeight r σ)
      ((1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ))) := by
  let : Finite (Eisensteinˣ) := metaplectic_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  have hq := metaplecticRamifiedRatio_bounds hσ
  have hk := hasSum_geometric_of_lt_one hq.1 hq.2
  have hw : Summable (fun w : PrimaryArgument => norm w^(-1-σ)) := by
    convert primary_norm_rpow_summable (show 1 < 1+σ by linarith) using 1
    ext w
    congr 1
    ring
  have hp : Summable (fun h : PrimaryArgument => norm h^(-3/2-3*σ)) := by
    convert primary_norm_rpow_summable (show 1 < 3/2+3*σ by linarith) using 1
    ext w
    congr 1
    ring
  have hpw := metaplectic_product_hasSum hp.hasSum hw.hasSum
    (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    (fun w => Real.rpow_nonneg (norm_nonneg w) _)
  have hh : HasSum (fun h : metaplecticPrimaryDivisors r => norm h.val^(-σ))
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by
    rw [←Finset.sum_coe_sort]
    exact hasSum_fintype _
  have hhpw := metaplectic_product_hasSum hh hpw
    (fun h => Real.rpow_nonneg (norm_nonneg h.val) _)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1) _)
      (Real.rpow_nonneg (norm_nonneg z.2) _))
  have hu : HasSum (fun _ : Eisensteinˣ => (1:ℝ)) (Nat.card (Eisensteinˣ):ℝ) := by
    simpa using (hasSum_fintype (fun _ : Eisensteinˣ => (1:ℝ)))
  have huh := metaplectic_product_hasSum hu hhpw (fun _ => zero_le_one)
    (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2) _)))
  have hall := metaplectic_product_hasSum hk huh (fun _ => pow_nonneg hq.1 _)
    (fun z => mul_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.1.val) _)
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg z.2.2.1) _)
        (Real.rpow_nonneg (norm_nonneg z.2.2.2) _))))
  change HasSum (fun z : MetaplecticCoefficientCode r => metaplecticCodeWeight r σ z) _
  simpa only [metaplecticCodeWeight,mul_assoc] using hall

lemma metaplecticCodeWeight_summable (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    Summable (metaplecticCodeWeight r σ) := (metaplecticCodeWeight_hasSum r hσ).summable

lemma metaplecticCodeWeight_tsum (r : Eisenstein) {σ : ℝ} (hσ : 0 < σ) :
    (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) =
      (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
      (∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ))*
      (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
      (∑' w : PrimaryArgument, norm w^(-1-σ)) :=
  (metaplecticCodeWeight_hasSum r hσ).tsum_eq

/-- The full separated majorant has an arbitrarily small level loss. -/
theorem metaplecticCodeWeight_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      (∑' z : MetaplecticCoefficientCode r, metaplecticCodeWeight r σ z) ≤ C*norm r^ε := by
  obtain ⟨D,hD,hdiv⟩ := metaplectic_divisor_weight_small_power hε hσ
  let A := (1-metaplecticRamifiedRatio σ)⁻¹*(Nat.card (Eisensteinˣ):ℝ)*
    (∑' h : PrimaryArgument, norm h^(-3/2-3*σ))*
    (∑' w : PrimaryArgument, norm w^(-1-σ))
  have hA : 0 ≤ A := by
    have hden : 0 ≤ 1-metaplecticRamifiedRatio σ :=
      sub_nonneg.mpr (metaplecticRamifiedRatio_bounds hσ).2.le
    have hp : 0 ≤ ∑' h : PrimaryArgument, norm h^(-3/2-3*σ) :=
      tsum_nonneg (fun h => Real.rpow_nonneg (norm_nonneg h) _)
    have hw : 0 ≤ ∑' w : PrimaryArgument, norm w^(-1-σ) :=
      tsum_nonneg (fun w => Real.rpow_nonneg (norm_nonneg w) _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hden) (Nat.cast_nonneg _)) hp) hw
  refine ⟨D*(A+1),mul_pos hD (by linarith),?_⟩
  intro r hr
  rw [metaplecticCodeWeight_tsum r hσ]
  calc
    _ = A*(∑ h ∈ metaplecticPrimaryDivisors r, norm h^(-σ)) := by dsimp [A]; ring
    _ ≤ A*(D*norm r^ε) := mul_le_mul_of_nonneg_left (hdiv r hr) hA
    _ ≤ D*(A+1)*norm r^ε := by nlinarith [Real.rpow_nonneg (norm_nonneg r) ε]

end CubicFirstMoment

end

end OAI
