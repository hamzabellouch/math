import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Finite character tests determine joint statistics

This is the finite Fourier inversion step in `sections/distribution.tex`.
It is an algebraic transfer lemma, not an assumed arithmetic decorrelation
result. The arithmetic correlation limits still have to be established.
-/

open Filter Finset Module
open scoped Topology

namespace JointDickman

/-- A finite weighted mean, as a linear statistic. -/
noncomputable def weightedMean {G : Type*} [Fintype G] (μ : G → ℂ) :
    (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ a, μ a * f a
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

/-- The product of the two marginal statistics. -/
noncomputable def productMean {G H : Type*}
    (μ : (G → ℂ) →ₗ[ℂ] ℂ) (ν : (H → ℂ) →ₗ[ℂ] ℂ) :
    (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g => μ f * ν g
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [mul_left_comm] }
  map_add' f g := by ext h; simp [add_mul]
  map_smul' c f := by ext h; simp [mul_assoc]

/-- The ordinary empirical joint statistic; `s` is the counting range and
`w` is the normalization. The observations may depend on the scale. -/
noncomputable def jointStatistic {G H : Type*} (s : Finset ℕ) (w : ℂ)
    (u : ℕ → G) (v : ℕ → H) :
    (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun g => w * ∑ n ∈ s, f (u n) * g (v n)
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm] }
  map_add' f g := by ext h; simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by ext h; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

private theorem linear_expansion {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Basis ι ℂ E)
    (L : E →ₗ[ℂ] ℂ) (v : E) :
    L v = ∑ i, b.repr v i * L (b i) := by
  calc
    L v = L (∑ i, b.repr v i • b i) := congrArg L (b.sum_repr v).symm
    _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

/-- Convergence of linear statistics on a finite basis determines every statistic. -/
theorem tendsto_linear_of_basis {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Basis ι ℂ E)
    (Q : ℕ → E →ₗ[ℂ] ℂ) (L : E →ₗ[ℂ] ℂ)
    (h : ∀ i, Tendsto (fun N => Q N (b i)) atTop (𝓝 (L (b i))))
    (v : E) : Tendsto (fun N => Q N v) atTop (𝓝 (L v)) := by
  simp_rw [linear_expansion b _ v]
  exact tendsto_finsetSum Finset.univ fun i _ => tendsto_const_nhds.mul (h i)

/-- Convergence on all pairs of finite basis vectors determines a bilinear statistic. -/
theorem tendsto_bilinear_of_bases {ι κ E F : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (b : Basis ι ℂ E) (c : Basis κ ℂ F)
    (Q : ℕ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (L : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ i j, Tendsto (fun N => Q N (b i) (c j)) atTop (𝓝 (L (b i) (c j))))
    (v : E) (w : F) : Tendsto (fun N => Q N v w) atTop (𝓝 (L v w)) := by
  have hb (i : ι) : Tendsto (fun N => Q N (b i) w) atTop (𝓝 (L (b i) w)) :=
    tendsto_linear_of_basis c (fun N => Q N (b i)) (L (b i)) (h i) w
  exact tendsto_linear_of_basis b (fun N => (Q N).flip w) (L.flip w) hb v

/-- For the finite bin-count group, character-pair limits imply limits for every
pair of bin events. This does not assert those character-pair limits. -/
theorem tendsto_of_character_pairs {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (Q : ℕ → (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ)
    (L : (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => Q N χ ψ) atTop (𝓝 (L χ ψ)))
    (f : G → ℂ) (g : H → ℂ) :
    Tendsto (fun N => Q N f g) atTop (𝓝 (L f g)) := by
  exact tendsto_bilinear_of_bases (AddChar.complexBasis G) (AddChar.complexBasis H)
    Q L (by simpa only [AddChar.complexBasis_apply] using h) f g

/-- The concrete empirical form of finite Fourier inversion. Every pair of
test functions has the product limit once every pair of characters does. -/
theorem jointStatistic_factorization {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (s : ℕ → Finset ℕ) (w : ℕ → ℂ) (u : ℕ → ℕ → G) (v : ℕ → ℕ → H)
    (μ : G → ℂ) (ν : H → ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => w N * ∑ n ∈ s N, χ (u N n) * ψ (v N n)) atTop
        (𝓝 ((∑ a, μ a * χ a) * (∑ b, ν b * ψ b))))
    (f : G → ℂ) (g : H → ℂ) :
    Tendsto (fun N => w N * ∑ n ∈ s N, f (u N n) * g (v N n)) atTop
      (𝓝 ((∑ a, μ a * f a) * (∑ b, ν b * g b))) := by
  exact tendsto_of_character_pairs
    (fun N => jointStatistic (s N) (w N) (u N) (v N))
    (productMean (weightedMean μ) (weightedMean ν)) h f g

/-- In particular, all pairs of events factor. These are precisely the
bin events used to test smoothness at rational powers. -/
theorem jointEvent_factorization {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (s : ℕ → Finset ℕ) (w : ℕ → ℂ) (u : ℕ → ℕ → G) (v : ℕ → ℕ → H)
    (μ : G → ℂ) (ν : H → ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => w N * ∑ n ∈ s N, χ (u N n) * ψ (v N n)) atTop
        (𝓝 ((∑ a, μ a * χ a) * (∑ b, ν b * ψ b))))
    (A : G → Prop) (B : H → Prop) [DecidablePred A] [DecidablePred B] :
    Tendsto (fun N => w N * ∑ n ∈ s N,
      (if A (u N n) ∧ B (v N n) then (1 : ℂ) else 0)) atTop
      (𝓝 ((∑ a with A a, μ a) * (∑ b with B b, ν b))) := by
  have hind (a : G) (b : H) :
      (if A a then (1 : ℂ) else 0) * (if B b then 1 else 0) =
        if A a ∧ B b then 1 else 0 := by
    by_cases ha : A a <;> by_cases hb : B b <;> simp [ha, hb]
  simpa only [hind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter] using
    jointStatistic_factorization s w u v μ ν h
      (fun a => if A a then 1 else 0) (fun b => if B b then 1 else 0)

end JointDickman

end OAI
