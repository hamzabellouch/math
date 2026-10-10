import Mathlib

namespace OAI

/-!
Self-adjoint operator estimates and the weighted-graph spectral trickling argument.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Spectral

section

lemma eigenvalue_trickle {lam μ : ℝ} (hlam : lam < 1) (hμ : μ < 1)
    (h : μ ≤ lam + (1-lam)*μ^2) : μ ≤ lam/(1-lam) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-lam)).mpr
  have hp : 0 < 1-μ := by linarith
  nlinarith [mul_pos hp (by linarith : 0 < 1-lam)]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem operator_trickle (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (c : E) (hfix : ∀ v, A v = v → ∃ t : ℝ, v = t • c)
    {lam : ℝ} (hlam : lam < 1)
    (hupper : ∀ v, ⟪A v,v⟫_ℝ ≤ ⟪v,v⟫_ℝ)
    (hlocal : ∀ v, ⟪A v,v⟫_ℝ ≤ lam*⟪v,v⟫_ℝ + (1-lam)*⟪A v,A v⟫_ℝ)
    (v : E) (hv : ⟪c,v⟫_ℝ = 0) :
    ⟪A v,v⟫_ℝ ≤ lam/(1-lam) * ⟪v,v⟫_ℝ := by
  classical
  let b := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let ev := hA.eigenvalues (n := Module.finrank ℝ E) rfl
  have he (i) : A (b i) = ev i • b i := hA.apply_eigenvectorBasis rfl i
  have hn (i) : ⟪b i,b i⟫_ℝ = 1 := by
    simp
  have hi (i) : ev i ≤ 1 := by
    have h := hupper (b i)
    rw [he,real_inner_smul_left,hn,mul_one] at h
    exact h
  have hbound (i) : ev i * (b.repr v i)^2 ≤ lam/(1-lam) * (b.repr v i)^2 := by
    by_cases h : ev i = 1
    · have hh : A (b i) = b i := by rw [he,h,one_smul]
      obtain ⟨t,ht⟩ := hfix (b i) hh
      have hvi : b.repr v i = 0 := by
        rw [OrthonormalBasis.repr_apply_apply,ht,real_inner_smul_left,hv,mul_zero]
      simp [hvi]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply eigenvalue_trickle hlam (lt_of_le_of_ne (hi i) h)
      have hl := hlocal (b i)
      rw [he,real_inner_smul_left,real_inner_smul_right,real_inner_smul_left,hn] at hl
      nlinarith
  have hrepr : ∀ i, b.repr (A v) i = ev i * b.repr v i :=
    hA.eigenvectorBasis_apply_self_apply rfl v
  rw [← b.repr.inner_map_map (A v) v, ← b.repr.inner_map_map v v]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hrepr]
  nlinarith [hbound i]

end

open scoped BigOperators InnerProductSpace
variable {V : Type} [Fintype V]

structure WeightedGraph (V : Type) [Fintype V] where
  edge : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ edge u v
  symm : ∀ u v, edge u v = edge v u
  row_pos : ∀ u, 0 < ∑ v, edge u v

namespace WeightedGraph
open WithLp
local instance : DecidableEq V := Classical.decEq _
variable (G : WeightedGraph V)
def mass (u : V) : ℝ := ∑ v, G.edge u v
def energy (f : V → ℝ) : ℝ := ∑ u, G.mass u * (f u)^2
def pairing (f g : V → ℝ) : ℝ := ∑ u, ∑ v, G.edge u v * f u * g v
def action (f : V → ℝ) (u : V) : ℝ := (∑ v, G.edge u v * f v) / G.mass u
def Connected : Prop := ∀ u v : V, Relation.ReflTransGen (fun u v => 0 < G.edge u v) u v

lemma mass_pos (u : V) : 0 < G.mass u := G.row_pos u
lemma mass_ne (u : V) : G.mass u ≠ 0 := ne_of_gt (G.mass_pos u)
lemma energy_nonneg (f : V → ℝ) : 0 ≤ G.energy f :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (G.mass_pos u).le (sq_nonneg _))

lemma swapped_energy (f : V → ℝ) :
    (∑ u, ∑ v, G.edge u v * (f v)^2) = G.energy f := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [mass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [G.symm]

lemma energy_difference (f : V → ℝ) :
    G.energy f - G.pairing f f = (1/2:ℝ) * ∑ u, ∑ v, G.edge u v * (f u-f v)^2 := by
  have hswap := G.swapped_energy f
  have hself : (∑ u, ∑ v, G.edge u v * (f u)^2) = G.energy f := by
    simp only [energy,mass,Finset.sum_mul]
  have he : (∑ u, ∑ v, G.edge u v * (f u-f v)^2) =
      (∑ u, ∑ v, G.edge u v * (f u)^2) + (∑ u, ∑ v, G.edge u v * (f v)^2) -
        2 * G.pairing f f := by
    simp only [pairing,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he,hself,hswap]
  ring

lemma pairing_le_energy (f : V → ℝ) : G.pairing f f ≤ G.energy f := by
  have hn : 0 ≤ ∑ u, ∑ v, G.edge u v * (f u-f v)^2 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      mul_nonneg (G.nonneg u v) (sq_nonneg _)))
  have hh := G.energy_difference f
  linarith

lemma action_pairing (f g : V → ℝ) :
    (∑ u, G.mass u * f u * G.action g u) = G.pairing f g := by
  unfold pairing action
  apply Finset.sum_congr rfl
  intro u _
  calc
    G.mass u * f u * ((∑ v, G.edge u v * g v)/G.mass u) =
        f u * (∑ v, G.edge u v * g v) := by field_simp [G.mass_ne u]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

lemma fixed_constant (hG : G.Connected) (f : V → ℝ) (hf : G.action f = f) :
    ∀ u v, f u = f v := by
  have he : G.energy f = G.pairing f f := by
    rw [← G.action_pairing, hf]
    simp only [energy,pow_two,mul_assoc]
  have hz : ∑ u, ∑ v, G.edge u v * (f u-f v)^2 = 0 := by
    have h := G.energy_difference f
    rw [he,sub_self] at h
    linarith
  have hn (u v) : 0 ≤ G.edge u v * (f u-f v)^2 :=
    mul_nonneg (G.nonneg u v) (sq_nonneg _)
  have hedge (u v) (huv : 0 < G.edge u v) : f u = f v := by
    have hrow : ∑ v, G.edge u v * (f u-f v)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => hn u v))).mp hz
        u (Finset.mem_univ u)
    have hs : G.edge u v * (f u-f v)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hn u v)).mp hrow v (Finset.mem_univ v)
    have hsq := (mul_eq_zero.mp hs).resolve_left (ne_of_gt huv)
    nlinarith [sq_nonneg (f u-f v)]
  intro u v
  induction hG u v with
  | refl => rfl
  | @tail b c _ hbc ih => exact ih.trans (hedge b c hbc)

def coord (f : V → ℝ) : EuclideanSpace ℝ V := toLp 2 (fun u => Real.sqrt (G.mass u) * f u)
def uncoord (v : EuclideanSpace ℝ V) : V → ℝ := fun u => v u / Real.sqrt (G.mass u)
def matrix : Matrix V V ℝ := fun u v => G.edge u v / (Real.sqrt (G.mass u)*Real.sqrt (G.mass v))
def operator : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := G.matrix.toEuclideanLin

lemma sqrt_ne (u : V) : Real.sqrt (G.mass u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (G.mass_pos u))
@[simp] lemma coord_uncoord (v : EuclideanSpace ℝ V) : G.coord (G.uncoord v) = v := by
  ext u
  simp only [coord,uncoord,PiLp.toLp_apply,mul_div_cancel₀ _ (G.sqrt_ne u)]
@[simp] lemma uncoord_coord (f : V → ℝ) : G.uncoord (G.coord f) = f := by
  funext u
  simp only [coord,uncoord,PiLp.toLp_apply,mul_div_cancel_left₀ _ (G.sqrt_ne u)]

lemma coord_inner (f g : V → ℝ) :
    ⟪G.coord f,G.coord g⟫_ℝ = ∑ u, G.mass u * f u * g u := by
  simp only [coord,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  apply Finset.sum_congr rfl
  intro u _
  calc
    _ = (Real.sqrt (G.mass u))^2 * f u * g u := by ring
    _ = _ := by rw [Real.sq_sqrt (G.mass_pos u).le]

lemma operator_coord (f : V → ℝ) : G.operator (G.coord f) = G.coord (G.action f) := by
  ext u
  change (∑ v, G.edge u v / (Real.sqrt (G.mass u)*Real.sqrt (G.mass v)) *
    (Real.sqrt (G.mass v)*f v)) = Real.sqrt (G.mass u)*((∑ v,G.edge u v*f v)/G.mass u)
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hs := Real.sq_sqrt (G.mass_pos u).le
  field_simp [G.sqrt_ne u,G.sqrt_ne v,G.mass_ne u]
  rw [hs]
  ring

lemma operator_symmetric : G.operator.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext u v
  simp only [Matrix.conjTranspose_apply,star_trivial,matrix]
  rw [G.symm v u,mul_comm]

theorem trickle [Nonempty V] (hG : G.Connected) {lam : ℝ} (hlam : lam < 1)
    (hloc : ∀ f : V → ℝ, G.pairing f f ≤ lam*G.energy f + (1-lam)*G.energy (G.action f))
    (f : V → ℝ) (hf : ∑ u, G.mass u * f u = 0) :
    G.pairing f f ≤ (lam/(1-lam))*G.energy f := by
  let c := G.coord (fun _ => 1)
  have hfix (v : EuclideanSpace ℝ V) (hv : G.operator v = v) : ∃ t : ℝ, v = t • c := by
    have hh : G.action (G.uncoord v) = G.uncoord v := by
      have h := congrArg G.uncoord hv
      rw [← G.coord_uncoord v,G.operator_coord,G.uncoord_coord] at h
      simpa using h
    let u : V := Classical.choice inferInstance
    refine ⟨G.uncoord v u,?_⟩
    conv_lhs => rw [← G.coord_uncoord v]
    ext w
    change Real.sqrt (G.mass w)*G.uncoord v w = G.uncoord v u * (Real.sqrt (G.mass w)*1)
    rw [G.fixed_constant hG _ hh w u]
    ring
  have hup (v : EuclideanSpace ℝ V) : ⟪G.operator v,v⟫_ℝ ≤ ⟪v,v⟫_ℝ := by
    rw [← G.coord_uncoord v,G.operator_coord,G.coord_inner,G.coord_inner]
    have h := G.pairing_le_energy (G.uncoord v)
    rw [← G.action_pairing] at h
    simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h
  have hlo (v : EuclideanSpace ℝ V) : ⟪G.operator v,v⟫_ℝ ≤
      lam*⟪v,v⟫_ℝ + (1-lam)*⟪G.operator v,G.operator v⟫_ℝ := by
    rw [← G.coord_uncoord v,G.operator_coord,G.coord_inner,G.coord_inner,G.coord_inner]
    have h := hloc (G.uncoord v)
    rw [← G.action_pairing] at h
    simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h
  have hmean : ⟪c,G.coord f⟫_ℝ = 0 := by simpa [c,G.coord_inner] using hf
  have h := operator_trickle G.operator G.operator_symmetric c hfix hlam hup hlo (G.coord f) hmean
  rw [G.operator_coord,G.coord_inner,G.coord_inner] at h
  rw [← G.action_pairing]
  simpa only [energy,pow_two,mul_assoc,mul_left_comm,mul_comm] using h

end WeightedGraph
end CoboundaryExpanders.Spectral

end

end OAI
