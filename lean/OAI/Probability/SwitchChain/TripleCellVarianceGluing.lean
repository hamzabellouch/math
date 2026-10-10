import OAI.Probability.SwitchChain.PairTripleBridge

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.CellVarianceGluing

variable {α κ : Type*} [sectionFintypeα : Fintype α] [sectionFintypeκ : Fintype κ]

def restrict (key : α → κ) (k : κ) :
    EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ {x // key x = k} where
  toFun f := WithLp.toLp 2 (fun x => f x.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include sectionFintypeα sectionFintypeκ in
@[simp] theorem restrict_apply (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) (x : {x // key x = k}) :
    restrict key k f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeκ := sectionFintypeκ
  exact rfl

theorem norm_sq_eq_sum_restrict (key : α → κ) (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ k, ‖restrict key k f‖ ^ 2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq]
  exact (Fintype.sum_fiberwise key (fun x => ‖f x‖ ^ 2)).symm

theorem norm_sum_sq_le_of_cells {ι : Type*} [Fintype ι]
    (key : α → κ) (y : ι → EuclideanSpace ℝ α) (c : ℝ)
    (hlocal : ∀ k, ‖∑ i, restrict key k (y i)‖ ^ 2 ≤
      c * ∑ i, ‖restrict key k (y i)‖ ^ 2) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  calc
    _ = ∑ k, ‖∑ i, restrict key k (y i)‖ ^ 2 := by
      rw [norm_sq_eq_sum_restrict key]
      simp only [map_sum]
    _ ≤ ∑ k, c * ∑ i, ‖restrict key k (y i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hlocal k)
    _ = c * ∑ i, ‖y i‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (norm_sq_eq_sum_restrict key (y i)).symm)

def cellSpace (key : α → κ) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, key x = key y → f x = f y}
  zero_mem' := by intro x y h; rfl
  add_mem' := by
    intro f g hf hg x y h
    change f x + g x = f y + g y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c * f x = c * f y
    rw [hf x y h]

def center (key : α → κ) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (cellSpace key).starProjection

include sectionFintypeκ in
theorem center_mem (key : α → κ) (f : EuclideanSpace ℝ α) :
    center key f ∈ cellSpace key := by
  have retainedsectionFintypeκ := sectionFintypeκ
  exact (cellSpace key).starProjection_apply_mem f

include sectionFintypeκ in
theorem sum_restrict_sub_center_eq_zero (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) :
    ∑ x : {x // key x = k}, restrict key k (f - center key f) x = 0 := by
  have retainedsectionFintypeκ := sectionFintypeκ
  classical
  let indicator : EuclideanSpace ℝ α :=
    WithLp.toLp 2 (fun x => if key x = k then 1 else 0)
  have hmem : indicator ∈ cellSpace key := by
    intro x y h
    change (if key x = k then (1 : ℝ) else 0) =
      (if key y = k then (1 : ℝ) else 0)
    rw [h]
  have horth := Submodule.starProjection_inner_eq_zero
    (K := cellSpace key) f indicator hmem
  change ⟪f - center key f, indicator⟫ = 0 at horth
  have horth' : (∑ x, if key x = k then (f - center key f) x else 0) = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, indicator,
      mul_ite] using horth
  have hsum : (∑ x ∈ Finset.univ.filter (fun x => key x = k),
      (f - center key f) x) = 0 := by
    simpa only [Finset.sum_filter] using horth'
  rw [Finset.sum_subtype (p := fun x => key x = k) _ (fun x => by simp)] at hsum
  exact hsum

theorem centered_row_variance_of_cells {ι : Type*} [Fintype ι]
    (key : α → κ) (P : ι → EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α)
    (Q : ∀ k, ι → EuclideanSpace ℝ {x // key x = k} →ₗ[ℝ]
      EuclideanSpace ℝ {x // key x = k})
    (htransport : ∀ i k f, restrict key k (P i f) = Q k i (restrict key k f))
    (c : ℝ)
    (hlocal : ∀ k (g : EuclideanSpace ℝ {x // key x = k}),
      (∑ x, g x) = 0 → ‖∑ i, Q k i g‖ ^ 2 ≤ c * ∑ i, ‖Q k i g‖ ^ 2)
    (f : EuclideanSpace ℝ α) :
    ‖∑ i, P i (f - center key f)‖ ^ 2 ≤
      c * ∑ i, ‖P i (f - center key f)‖ ^ 2 := by
  apply norm_sum_sq_le_of_cells key
  intro k
  simp only [htransport]
  exact hlocal k _ (sum_restrict_sub_center_eq_zero key k f)

end Problem315.CellVarianceGluing

namespace Problem315.PairResampling
open CellVarianceGluing

theorem expectation_center_of_key_invariant
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (key : GraphState n d → κ) (a : Finset (Fin n))
    (hkey : ∀ G H : GraphState n d, SameFiber a G.val H.val → key G = key H)
    (f : StateSpace n d) : expectation n d a (center key f) = center key f := by
  apply (expectation_eq_self_iff a _).mpr
  intro G H h
  exact center_mem key f G H (hkey G H h)

theorem vertex_triple_square_of_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ} {κ : Type*} [Fintype κ]
    (T : Finset (Fin n)) (hT : T.card = 3)
    (key : GraphState n d → κ)
    (hkey : ∀ a ∈ T.powersetCard 2, ∀ G H : GraphState n d,
      SameFiber a G.val H.val → key G = key H)
    (hlocal : ∀ k (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict key k (expectation n d a.val (f - center key f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict key k (expectation n d a.val (f - center key f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_row_variance T hT (center key)
  · intro a ha f
    exact expectation_center_of_key_invariant key a (hkey a ha) f
  · intro f
    have h := norm_sum_sq_le_of_cells key
      (fun a : T.powersetCard 2 => expectation n d a.val (f - center key f)) 2
      (fun k => hlocal k f)
    simpa only [Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => expectation n d a (f - center key f)),
      Finset.sum_coe_sort (T.powersetCard 2)
      (fun a => ‖expectation n d a (f - center key f)‖ ^ 2)] using h

end Problem315.PairResampling

namespace Problem315.PairResampling
open CellVarianceGluing

def tripleExteriorKey {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n))
    (G : GraphState n d) : SimpleGraph {v : Fin n // v ∉ T} :=
  G.val.comap Subtype.val

theorem tripleExteriorKey_eq_of_sameFiber {n : ℕ} {d : Fin n → ℕ}
    {T a : Finset (Fin n)} (ha : a ⊆ T) (G H : GraphState n d)
    (h : SameFiber a G.val H.val) : tripleExteriorKey T G = tripleExteriorKey T H := by
  ext u v
  exact h.1 u.val (fun hu => u.property (ha hu))
    v.val (fun hv => v.property (ha hv))

theorem expectation_tripleExterior_center {n : ℕ} {d : Fin n → ℕ}
    {T a : Finset (Fin n)} (ha : a ⊆ T) (f : StateSpace n d) :
    expectation n d a (center (tripleExteriorKey T) f) =
      center (tripleExteriorKey T) f := by
  exact expectation_center_of_key_invariant (tripleExteriorKey T) a
    (fun G H h => tripleExteriorKey_eq_of_sameFiber ha G H h) f

theorem vertex_triple_square_of_exterior_cellwise_row_variance
    {n : ℕ} {d : Fin n → ℕ}
    (T : Finset (Fin n)) (hT : T.card = 3)
    (hlocal : ∀ (k : SimpleGraph {v : Fin n // v ∉ T}) (f : StateSpace n d),
      ‖∑ a : T.powersetCard 2,
        restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2 ≤
      2 * ∑ a : T.powersetCard 2,
        ‖restrict (tripleExteriorKey T) k
          (expectation n d a.val (f - center (tripleExteriorKey T) f))‖ ^ 2) :
    ∀ f, ⟪f, ∑ a ∈ T.powersetCard 2, fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, fluctuation n d a f‖ ^ 2 := by
  apply vertex_triple_square_of_cellwise_row_variance T hT (tripleExteriorKey T) _ hlocal
  intro a ha G H h
  exact tripleExteriorKey_eq_of_sameFiber (Finset.mem_powersetCard.mp ha).1 G H h

end Problem315.PairResampling

end

end OAI
