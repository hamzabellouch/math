import OAI.MeasureTheory.SelfSimilar.FiniteRefinement

namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

noncomputable def Law.bandSupport (ν : Law) : Finset ℤ := by
  classical
  exact (ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2-e.1|)

noncomputable def Law.bandCost (ν : Law) (R : ℝ) : ℝ := by
  classical
  exact ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ R),
    (2 : ℝ)^(1-ℓ)*capacity ν ℓ

theorem Law.support_nonempty (ν : Law) : ν.support.Nonempty := by
  by_contra h
  have := ν.prob_sum
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at this
  norm_num at this

theorem Law.subtype_sum (ν : Law) : ∑ a : ν.support, ν.prob a = 1 := by
  simpa only [Finset.sum_coe_sort] using ν.prob_sum

theorem mass_support {β : Type uβ} [DecidableEq β] (ν : Law) (g : ℝ → β) (b : β) :
    mass Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) b =
      mass ν.support ν.prob g b := by
  classical
  simp only [mass, Finset.sum_filter]
  exact Finset.sum_coe_sort ν.support (fun a => if g a = b then ν.prob a else 0)

theorem sum_support₂ (ν : Law) (f : ℝ → ℝ → ℝ) :
    (∑ a : ν.support, ∑ b : ν.support, f a b) = ∑ a ∈ ν.support, ∑ b ∈ ν.support, f a b := by
  calc
    _ = ∑ a : ν.support, ∑ b ∈ ν.support, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort ν.support (f a)
    _ = _ := Finset.sum_coe_sort ν.support (fun a => ∑ b ∈ ν.support, f a b)

theorem mean_deviation_le_bandCost {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (R : ℝ)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    (∑ a : ν.support, ν.prob a * |(a : ℝ)-FiniteRefinement.cellMean
      (fun b : ν.support => ν.prob b) (fun b => (b : ℝ)) (fun b => g b) (g a)|) ≤
      ν.bandCost R := by
  classical
  have hj := FiniteRefinement.mean_deviation_le_coupling
    (fun a : ν.support => ν.prob a) (fun a => (a : ℝ)) (fun a => g a)
    (fun a => ν.prob_pos a a.property)
  have he : (∑ a : ν.support, ∑ b : ν.support,
      (if g a = g b then ν.prob a*ν.prob b /
        mass Finset.univ (fun x : ν.support => ν.prob x) (fun x => g x) (g a) else 0)*
      |(a : ℝ)-(b : ℝ)|) =
      ∑ a ∈ ν.support, ∑ b ∈ ν.support, conditionalCoupling ν g a b * |b-a| := by
    simp only [mass_support, conditionalCoupling, abs_sub_comm]
    exact sum_support₂ ν (fun a b => (if g a = g b then ν.prob a*ν.prob b /
      mass ν.support ν.prob g (g a) else 0) * |a-b|)
  rw [he] at hj
  apply hj.trans
  exact coupling_distance_le (conditionalCoupling ν g) R
    (fun x hx y hy => conditionalCoupling_nonneg ν g hx hy)
    (fun x _ y _ => conditionalCoupling_symm ν g x y)
    (fun x hx => (conditionalCoupling_row ν g hx).le)
    (by
      intro x hx y hy hxy
      apply conditionalCoupling_eq_zero_of_ne
      intro he
      have hh := hd x hx y hy he
      rw [abs_sub_comm] at hh
      exact (not_le_of_gt hxy) hh)

theorem exists_capacity_refinement (ν : Law) (g : ℝ → List ℤ)
    (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 < R)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    ∃ g' : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g' a = g' b → |a-b| ≤ R/4) ∧
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g' (x i)) (fun x => ∑ i, (x i : ℝ)) ≤
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ)) +
      (352*k^4/R)*ν.bandCost R*Real.log 2 := by
  classical
  let p : ν.support → ℝ := fun a => ν.prob a
  have hp : ∀ a, 0 < p a := fun a => ν.prob_pos a a.property
  obtain ⟨u,hu⟩ := FiniteRefinement.exists_entropy_step p (fun a => (a : ℝ)) (fun a => g a)
    hp ν.subtype_sum k hk (R/4) (by positivity) (by
      intro a b hab
      simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hd a a.property b b.property hab)
  refine ⟨fun a => RandomGrid.cell (R/4) u a :: g a, ?_, ?_⟩
  · intro a _ b _ he
    exact (RandomGrid.cell_eq_distance_lt (by positivity) u (List.cons.inj he).1).le
  · rw [FiniteRefinement.refinement_increment p (fun a => (a : ℝ)) (fun a => g a)
      (fun a => (hp a).le) k (R/4) u]
    apply add_le_add le_rfl
    apply hu.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mean_deviation_le_bandCost ν g R hd)
        (by positivity : 0 ≤ (88 : ℝ)*k^4/(R/4)))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    convert hh using 1; ring

noncomputable def Law.partitionEntropy (ν : Law) (k : ℕ) (g : ℝ → List ℤ) : ℝ := by
  classical
  exact conditionalEntropy Finset.univ
    (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
    (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ))

noncomputable def Law.refinementCost (ν : Law) (k : ℕ) (R : ℝ) : ℝ :=
  (352*k^4/R)*ν.bandCost R*Real.log 2

theorem exists_fine_partition (ν : Law) (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    ∃ g : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ ρ/4^J) ∧
      ν.partitionEntropy k g ≤ ν.partitionEntropy k (fun x => [⌊x/ρ⌋]) +
        ∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h) := by
  classical
  induction J with
  | zero =>
    refine ⟨fun x => [⌊x/ρ⌋], ?_, ?_⟩
    · intro a _ b _ he
      have hh : RandomGrid.cell ρ 0 a = RandomGrid.cell ρ 0 b := by
        simpa only [RandomGrid.cell, RandomGrid.shift_zero, add_zero] using (List.cons.inj he).1
      simpa only [pow_zero, div_one] using (RandomGrid.cell_eq_distance_lt hρ 0 hh).le
    · simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ J ih =>
    obtain ⟨g,hd,hg⟩ := ih
    obtain ⟨g',hd',hg'⟩ := exists_capacity_refinement ν g k hk (ρ/4^J) (by positivity) hd
    refine ⟨g', ?_, ?_⟩
    · intro a ha b hb he
      simpa only [pow_succ, div_div] using hd' a ha b hb he
    · change ν.partitionEntropy k g' ≤ ν.partitionEntropy k g + ν.refinementCost k (ρ/4^J) at hg'
      rw [Finset.sum_range_succ]
      linarith

theorem exists_separating_depth (ν : Law) (ρ : ℝ) :
    ∃ J : ℕ, ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
  classical
  have ht : Filter.Tendsto (fun n : ℕ => ρ/(4 : ℝ)^n) Filter.atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1 : ℝ)/4 < 1)).const_mul ρ
    simpa only [div_pow, one_pow, mul_zero, div_eq_mul_inv, one_mul, inv_pow] using hh
  have he : ∀ᶠ J : ℕ in Filter.atTop,
      ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
    apply (Filter.eventually_all_finset ν.support).mpr
    intro a ha
    apply (Filter.eventually_all_finset ν.support).mpr
    intro b hb
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun _ h => (h hab).elim)
    · exact (ht.eventually (isOpen_Iio.mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hab)))).mono
        (fun J h _ => h)
  exact he.exists

theorem dyadic_upper_eq (ℓ : ℤ) : (2 : ℝ)^(1-ℓ) = 2*(2 : ℝ)^(-ℓ) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]

theorem band_scale_sum (ρ : ℝ) (hρ : 0 < ρ) (ℓ : ℤ) (J : ℕ) :
    (∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
      (2 : ℝ)^(1-ℓ)/(ρ/4^h)) ≤ if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0 := by
  classical
  let s := (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h)
  have hpow : ∀ h : ℕ, (0 : ℝ) < 4^h := fun h => pow_pos (by norm_num) h
  have hs : ∀ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h ≤ 2 := by
    intro h hh
    have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
    rw [dyadic_upper_eq]
    have he' : (2*(2 : ℝ)^(-ℓ)*4^h)/ρ ≤ 2 :=
      (div_le_iff₀ hρ).mpr (by nlinarith)
    convert he' using 1; ring
  have hgeom := geometric_fine_scale_bound s
    (div_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hρ.le) hs
  have heq : (∑ h ∈ s, (2 : ℝ)^(1-ℓ)/(ρ/4^h)) =
      ∑ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h := by
    apply Finset.sum_congr rfl
    intro h _
    field_simp
  change (∑ h ∈ s, _) ≤ _
  rw [heq]
  by_cases hℓ : (2 : ℝ)^(-ℓ) ≤ ρ
  · rw [ite_eq_left hℓ]
    exact hgeom
  · rw [ite_eq_right hℓ]
    have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
      have hone : (1 : ℝ) ≤ 4^h := one_le_pow₀ (by norm_num)
      have hlower : (2 : ℝ)^(-ℓ) ≤ (2 : ℝ)^(-ℓ)*4^h :=
        le_mul_of_one_le_right (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hone
      exact hℓ (hlower.trans he)
    simp only [hempty, Finset.sum_empty, le_refl]

theorem sum_refinementCost_le (ν : Law) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) ≤
      60000*k^4*Real.log 2 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ),
        capacity ν ℓ := by
  classical
  let C : ℝ := 352*k^4*Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) =
      C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        ∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
          (2 : ℝ)^(1-ℓ)/(ρ/4^h) := by
    simp only [Law.refinementCost, Law.bandCost, Finset.sum_filter, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [C]
    split_ifs <;> ring
  rw [he]
  have hpoint := Finset.sum_le_sum (s := ν.bandSupport) (fun ℓ _ =>
    mul_le_mul_of_nonneg_left (band_scale_sum ρ hρ ℓ J) (capacity_nonneg ν ℓ))
  calc
    _ ≤ C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        (if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0) := mul_le_mul_of_nonneg_left hpoint hC
    _ = (C*(8/3)) * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      split_ifs <;> ring
    _ ≤ (60000*k^4*Real.log 2) *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun ℓ _ => capacity_nonneg ν ℓ))
      dsimp only [C]
      have hn : 0 ≤ (k : ℝ)^4*Real.log 2 := by positivity
      nlinarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ℓ hℓ
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hℓ).1,
          (Finset.mem_filter.mp hℓ).2.trans (by linarith)⟩
      · intro ℓ _ _
        exact capacity_nonneg ν ℓ

theorem observableEntropy_support {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) :
    observableEntropy Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) =
      observableEntropy ν.support ν.prob g := by
  classical
  have he : (Finset.univ : Finset ν.support).image (fun a : ν.support => g (a : ℝ)) = ν.support.image g := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,_,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨a,a.property,hab⟩
    · intro hb
      obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,hab⟩
  simp only [observableEntropy, he, entropy, mass_support]

noncomputable def Law.sumset (ν : Law) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun x : Fin k → ν.support => ∑ i, (x i : ℝ))

theorem pair_bound_natural (ν : Law) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    k * (entropy ν.support ν.prob - observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋)) ≤
      Real.log (ν.sumset k).card + 60000*k^4*Real.log 2 *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ := by
  classical
  obtain ⟨a,ha⟩ := ν.support_nonempty
  have : Nonempty ν.support := ⟨⟨a,ha⟩⟩
  let p : ν.support → ℝ := fun a => ν.prob a
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let Y : (Fin k → ν.support) → ℝ := fun x => ∑ i, (x i : ℝ)
  let C₀ : (Fin k → ν.support) → Fin k → List ℤ := fun x i => [⌊(x i : ℝ)/ρ⌋]
  have hp : ∀ a, 0 ≤ p a := fun a => (ν.prob_pos a a.property).le
  have hw : ∀ x ∈ (Finset.univ : Finset (Fin k → ν.support)), 0 ≤ w x :=
    fun x _ => ProductLaw.weight_nonneg _ (fun _ a => hp a) x
  have hw1 : ∑ x, w x = 1 := ProductLaw.weight_sum _ (fun _ => ν.subtype_sum)
  obtain ⟨J,hJ⟩ := exists_separating_depth ν ρ
  obtain ⟨g,hd,hg⟩ := exists_fine_partition ν k hk ρ hρ J
  let G : (Fin k → ν.support) → Fin k → List ℤ := fun x i => g (x i)
  have hi : Function.Injective (fun a : ν.support => g a) := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    exact (not_lt_of_ge (hd a a.property b b.property he)) (hJ a a.property b b.property hab)
  have hG : Function.Injective G := by
    intro x y he
    funext i
    exact hi (congrFun he i)
  have hent : observableEntropy Finset.univ w G = k*entropy ν.support ν.prob := by
    rw [observableEntropy_of_injective Finset.univ w G hw hG, ProductLaw.entropy _ (fun _ => ν.subtype_sum)]
    have he : entropy Finset.univ p = entropy ν.support ν.prob :=
      Finset.sum_coe_sort ν.support (fun a => Real.negMulLog (ν.prob a))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (fun z => (k : ℝ)*z) he
  have hinit : observableEntropy Finset.univ w C₀ =
      k*observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) := by
    rw [ProductLaw.observable_entropy p (fun a : ν.support => [⌊(a : ℝ)/ρ⌋]) hp ν.subtype_sum]
    simp only [Fintype.card_fin]
    rw [observableEntropy_support ν (fun a => [⌊a/ρ⌋])]
    congr 1
    apply observableEntropy_eq_of_fibers _ _ _ _ (fun x hx => (ν.prob_pos x hx).le)
    intro x _ y _
    simp only [List.cons.injEq, and_true]
  have hy : observableEntropy Finset.univ w Y ≤ Real.log (ν.sumset k).card :=
    observableEntropy_le_log_on_superset Finset.univ (ν.sumset k) w Y
      (fun x _ => Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩) hw hw1
  have hjoint := observableEntropy_fst_le Finset.univ w G Y hw
  have hcinit := conditionalEntropy_le Finset.univ w C₀ Y hw hw1
  have hsum := sum_refinementCost_le ν k ρ hρ J
  change conditionalEntropy Finset.univ w G Y ≤ conditionalEntropy Finset.univ w C₀ Y + _ at hg
  rw [hent] at hjoint
  rw [hinit] at hcinit
  unfold conditionalEntropy at hg hcinit
  linarith

noncomputable def Law.shannonEntropy (ν : Law) : ℝ := entropy ν.support ν.prob / Real.log 2

noncomputable def Law.gridEntropy (ν : Law) (ρ : ℝ) : ℝ := by
  classical
  exact observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) / Real.log 2

theorem pair_bound (ν : Law) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    k*(ν.shannonEntropy-ν.gridEntropy ρ) ≤ Real.log (ν.sumset k).card / Real.log 2 +
      60000*k^4 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (div_le_div_iff_of_pos_right hl).mpr (pair_bound_natural ν k hk ρ hρ)
  dsimp only [Law.shannonEntropy, Law.gridEntropy]
  calc
    _ = (k*(entropy ν.support ν.prob-observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋))) /
        Real.log 2 := by ring
    _ ≤ (Real.log (ν.sumset k).card + 60000*k^4*Real.log 2 *
          ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ) / Real.log 2 := h
    _ = _ := by field_simp

end FairPairs

end EntropyRateDimension
end

end OAI
