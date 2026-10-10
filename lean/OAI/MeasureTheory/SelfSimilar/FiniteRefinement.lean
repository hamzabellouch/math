import OAI.MeasureTheory.SelfSimilar.GridCoupling

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def cellMean (p : α → ℝ) (v : α → ℝ) (g : α → β) (b : β) : ℝ :=
  ∑ a, ((if g a = b then p a else 0) / mass Finset.univ p g b) * v a

theorem distance_mean_le (p : α → ℝ) (v : α → ℝ) (z R : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hR : ∀ a, p a ≠ 0 → |z-v a| ≤ R) : |z - ∑ a, p a * v a| ≤ R := by
  have he : z - ∑ a, p a * v a = ∑ a, p a * (z-v a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ a, |p a * (z-v a)|) ≤ ∑ a, p a * R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hp a)]
      by_cases ha : p a = 0
      · simp only [ha, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hR a ha) (hp a)
    _ = R := by rw [← Finset.sum_mul, hp1, one_mul]

omit [Fintype α] in
theorem mass_pos {γ : Type uγ} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (g : α → γ) (hp : ∀ a ∈ s, 0 < p a) {b : γ} (hb : b ∈ s.image g) :
    0 < mass s p g b := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact (hp a ha).trans_le (Finset.single_le_sum
    (fun x hx => (hp x (Finset.mem_filter.mp hx).1).le) (by simp [ha]))

theorem cellMass_eq (p : α → ℝ) (g : α → β) {k : ℕ} (c : Fin k → β) (i : Fin k) :
    ProductLaw.cellMass (fun _ : Fin k => p) (fun _ => g) c i = mass Finset.univ p g (c i) := by
  simp only [ProductLaw.cellMass, mass, Finset.sum_filter]

theorem conditional_mean_eq (p : α → ℝ) (v : α → ℝ) (g : α → β)
    {k : ℕ} (c : Fin k → β) (i : Fin k) :
    (∑ a, ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c i a * v a) =
      cellMean p v g (c i) := by
  simp only [cellMean, ProductLaw.conditional, cellMass_eq]

theorem conditional_mean_distance_le (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 ≤ p a) {k : ℕ} (c : Fin k → β) (i : Fin k)
    (hc : mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) c ≠ 0) (x : α) (hx : g x = c i) (R : ℝ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ R) :
    |v x-cellMean p v g (c i)| ≤ R := by
  rw [← conditional_mean_eq p v g c i]
  apply distance_mean_le _ _ _ R
    (ProductLaw.conditional_nonneg _ _ _ (fun _ a => hp a) i)
    (ProductLaw.conditional_sum _ _ _ hc i)
  intro a ha
  have hga : g a = c i := by
    by_contra hn
    exact ha (by simp only [ProductLaw.conditional, ite_eq_right hn, zero_div])
  exact hd x a (hx.trans hga.symm)

theorem fiber_entropy_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) (u : AddCircle (1 : ℝ))
    (c : Fin k → β)
    (hc : c ∈ (Finset.univ : Finset (Fin k → α)).image (fun x i => g (x i))) :
    conditionalEntropy (Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c))
      (fun x => ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c)
      (fun x i => RandomGrid.cell δ u (v (x i))) (fun x => ∑ i, v (x i)) ≤
    11*k*(∑ x ∈ Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c),
      (ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c) *
      ∑ i, ∑ j, RandomGrid.hit (-(cellMean p v g (c j)/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (c i)|/δ) u)*Real.log 2 := by
  classical
  let w : (Fin k → α) → ℝ := ProductLaw.weight (fun _ : Fin k => p)
  let G : (Fin k → α) → (Fin k → β) := fun x i => g (x i)
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : 0 < mass Finset.univ w G c := mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hnc : mass Finset.univ w G c ≠ 0 := ne_of_gt hP
  let s₀ : Finset (Fin k → α) := Finset.univ.filter (fun x => G x = c)
  let p₀ : (Fin k → α) → ℝ := fun x => w x / mass Finset.univ w G c
  let v₀ : (Fin k → α) → Fin k → ℝ := fun x i => v (x i)
  let m₀ : Fin k → ℝ := fun i => cellMean p v g (c i)
  have hp₀ : ∀ x ∈ s₀, 0 ≤ p₀ x := fun x _ => div_nonneg (hw x).le hP.le
  have hp₀1 : ∑ x ∈ s₀, p₀ x = 1 := by
    rw [show (∑ x ∈ s₀, p₀ x) = mass Finset.univ w G c / mass Finset.univ w G c by
      exact (Finset.sum_div _ _ _).symm]
    exact div_self hnc
  have hv₀ : ∀ x ∈ s₀, ∀ i, |v₀ x i-m₀ i| ≤ 4*δ := by
    intro x hx i
    have he : G x = c := (Finset.mem_filter.mp hx).2
    exact conditional_mean_distance_le p v g (fun a => (hp a).le) c i hnc (x i)
      (congrFun he i) (4*δ) hd
  have hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| ∧ a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) =
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| then p₀ x else 0) *
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) := by
    intro a i j hij
    let E := fun (i : Fin k) (x : α) => a/(4*k) ≤ |v x-cellMean p v g (c i)|
    have heen := ProductLaw.two_coordinate_events
      (ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c) E
      (ProductLaw.conditional_sum _ _ _ hnc) i j hij
    rw [← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i) ∧ E j (x j)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E j (x j))] at heen
    exact heen
  exact RandomGrid.refinement_entropy_hit_bound s₀ p₀ k hk v₀ m₀ δ hδ u hp₀ hp₀1 hv₀ hind

theorem entropy_step_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ)
    (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    11*k*(∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x * ∑ i, ∑ j,
      RandomGrid.hit (-(cellMean p v g (g (x j))/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (g (x i))|/δ) u)*Real.log 2 := by
  classical
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let G := fun (x : Fin k → α) i => g (x i)
  let Y := fun (x : Fin k → α) => ∑ i, v (x i)
  let C := fun (x : Fin k → α) i => RandomGrid.cell δ u (v (x i))
  let P := mass Finset.univ w G
  let M := fun (c : Fin k → β) i => cellMean p v g (c i)
  let cost := fun (c : Fin k → β) (x : Fin k → α) => ∑ i, ∑ j,
    RandomGrid.hit (-(M c j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v (x i)-M c i|/δ) u
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : ∀ c ∈ Finset.univ.image G, 0 < P c :=
    fun c hc => mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hcstep : ∀ c ∈ Finset.univ.image G,
      conditionalEntropy (Finset.univ.filter (fun x => G x = c)) (fun x => w x/P c) C Y ≤
        11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2 :=
    fun c hc => fiber_entropy_hit_bound p v g hp k hk δ hδ hd u c hc
  rw [conditionalEntropy_disintegrate Finset.univ w C G Y (fun x _ => (hw x).le)]
  calc
    _ ≤ ∑ c ∈ Finset.univ.image G, P c *
        (11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcstep c hc) (hP c hc).le
    _ = 11*k*(∑ c ∈ Finset.univ.image G,
        ∑ x ∈ Finset.univ.filter (fun x => G x = c), w x*cost (G x) x)*Real.log 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      field_simp [ne_of_gt (hP c hc)]
    _ = _ := by
      rw [Finset.sum_fiberwise_of_maps_to (fun x (_ : x ∈ Finset.univ) => Finset.mem_image_of_mem G (Finset.mem_univ x))]

theorem mean_deviation_le_coupling (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) :
    (∑ a, p a * |v a-cellMean p v g (g a)|) ≤
      ∑ a, ∑ b, (if g a = g b then p a*p b/mass Finset.univ p g (g a) else 0) *
        |v a-v b| := by
  classical
  apply Finset.sum_le_sum
  intro a _
  have hP : 0 < mass Finset.univ p g (g a) :=
    mass_pos Finset.univ p g (fun x _ => hp x) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let q : α → ℝ := fun b => (if g b = g a then p b else 0)/mass Finset.univ p g (g a)
  have hq : ∀ b, 0 ≤ q b := by
    intro b
    exact div_nonneg (by split_ifs <;> first | exact (hp b).le | exact le_rfl) hP.le
  have hq1 : ∑ b, q b = 1 := by
    dsimp only [q]
    rw [← Finset.sum_div]
    simpa only [mass, Finset.sum_filter] using div_self (ne_of_gt hP)
  have he : v a-cellMean p v g (g a) = ∑ b, q b*(v a-v b) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul]
    rfl
  rw [he]
  calc
    p a * |∑ b, q b*(v a-v b)| ≤ p a * ∑ b, |q b*(v a-v b)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hp a).le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (hq b)]
      dsimp only [q]
      by_cases hg : g a = g b
      · simp only [hg, ite_true]
        ring
      · simp only [hg, Ne.symm hg, ite_false, zero_div, mul_zero, zero_mul]

theorem product_mean_deviation (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp1 : ∑ a, p a = 1) (k : ℕ) :
    (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      ∑ i, |v (x i)-cellMean p v g (g (x i))|) =
      k * ∑ a, p a*|v a-cellMean p v g (g a)| := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin k, (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      |v (x i)-cellMean p v g (g (x i))|) = ∑ a, p a*|v a-cellMean p v g (g a)| := by
    intro i
    simpa only [Finset.prod_singleton] using ProductLaw.moment (fun _ : Fin k => p)
      (fun _ a => |v a-cellMean p v g (g a)|) {i} (fun _ => hp1)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem exists_entropy_step (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) :
    ∃ u : AddCircle (1 : ℝ),
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    (88*k^4/δ)*(∑ a, p a*|v a-cellMean p v g (g a)|)*Real.log 2 := by
  classical
  obtain ⟨u,hu⟩ := RandomGrid.exists_shift_variation_bound Finset.univ
    (ProductLaw.weight (fun _ : Fin k => p)) k (fun x i => v (x i))
    (fun x i => cellMean p v g (g (x i))) δ hδ
    (fun x _ => ProductLaw.weight_nonneg _ (fun _ a => (hp a).le) x)
  refine ⟨u, (entropy_step_hit_bound p v g hp k hk δ hδ hd u).trans ?_⟩
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (11 : ℝ)*k))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [product_mean_deviation p v g hp1 k] at hm
  convert hm using 1; ring

theorem refinement_increment (p : α → ℝ) (v : α → ℝ) (g : α → List ℤ)
    (hp : ∀ a, 0 ≤ p a) (k : ℕ) (δ : ℝ) (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)) :: g (x i)) (fun x => ∑ i, v (x i)) =
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) (fun x => ∑ i, v (x i)) +
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) := by
  classical
  let w : (Fin k → α) → ℝ := ProductLaw.weight (fun _ : Fin k => p)
  let G := fun (x : Fin k → α) i => g (x i)
  let C := fun (x : Fin k → α) i => RandomGrid.cell δ u (v (x i))
  let Y := fun (x : Fin k → α) => ∑ i, v (x i)
  have hw : ∀ x ∈ (Finset.univ : Finset (Fin k → α)), 0 ≤ w x :=
    fun x _ => ProductLaw.weight_nonneg _ (fun _ a => hp a) x
  have he := conditionalEntropy_eq_of_fibers Finset.univ w
    (fun x i => C x i :: G x i) (fun x => (C x,G x)) Y hw (by
      intro x _ y _
      constructor
      · intro h
        apply Prod.ext
        · funext i
          exact (List.cons.inj (congrFun h i)).1
        · funext i
          exact (List.cons.inj (congrFun h i)).2
      · intro h
        rw [Prod.mk.injEq] at h
        rw [h.1,h.2])
  rw [he, conditionalEntropy_chain Finset.univ w C G Y hw,
    conditionalEntropy_condition_swap Finset.univ w C G Y hw]

end FiniteRefinement

end EntropyRateDimension
end

end OAI
