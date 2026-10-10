import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.FlatDirection
import OAI.MathematicalPhysics.PEPSSubvolume.TwoFactors

namespace OAI

/-! Mixed singular residual bounds from simultaneous perturbations. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.ActualKernel
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.KernelPerturbation
open PolynomialPEPS.Subvolume.KernelNormalization PolynomialPEPS.Subvolume.OptimizerGauge
variable {L q : ℕ}

theorem real_complex_smul (t : ℝ) (v : State L q) : (t : ℂ) • v = t • v := by
  ext i
  simp [Complex.real_smul]

theorem two_affine_output (A : ℕ → Operator L q) (k l n : ℕ)
    (hk : k<n) (hl : l<n) (hkl : k ≠ l) (B C : Operator L q)
    (s t c d : ℂ) (ψ : State L q) :
    asMap (L := L) (q := q) (orderedPrefix
      (Function.update (Function.update A k (c • (A k+s • B)))
        l (d • (A l+t • C))) n) ψ =
      (c*d) • (asMap (L := L) (q := q) (orderedPrefix A n) ψ +
        s • asMap (L := L) (q := q) (orderedPrefix (Function.update A k B) n) ψ +
        t • asMap (L := L) (q := q) (orderedPrefix (Function.update A l C) n) ψ +
        (s*t) • asMap (L := L) (q := q)
          (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ) := by
  rw [two_affine_prefix A k l n hk hl hkl]
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (_ • (_ + _ + _ + _)) ψ = _
  simp only [map_smul, map_add, smul_apply, add_apply]
  rfl

theorem two_affine_kernel_output (A : ℕ → Operator L q) (k l n : ℕ)
    (hk : k<n) (hl : l<n) (hkl : k ≠ l) (B C : Operator L q) (ψ : State L q)
    (hkzero : asMap (L := L) (q := q) (orderedPrefix (Function.update A k B) n) ψ = 0)
    (ζ : ℂ) (c t b d : ℝ) :
    asMap (L := L) (q := q) (orderedPrefix
      (Function.update (Function.update A k
        ((b : ℂ) • (A k + (((c*t : ℝ) : ℂ)*ζ) • B))) l
        ((d : ℂ) • (A l + ((t : ℂ)*Complex.I) • C))) n) ψ =
      ((b*d : ℝ) : ℂ) • (asMap (L := L) (q := q) (orderedPrefix A n) ψ +
        t • (Complex.I • asMap (L := L) (q := q) (orderedPrefix (Function.update A l C) n) ψ) +
        (c*t^2) • ((ζ*Complex.I) • asMap (L := L) (q := q)
          (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ)) := by
  rw [two_affine_output A k l n hk hl hkl, hkzero,smul_zero,add_zero, Complex.ofReal_mul]
  simp only [← real_complex_smul,smul_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  congr 2
  ring_nf

theorem mixed_scalar_bound (N M S p d t : ℝ) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hS : 1 ≤ S) (hp : 2 < p) (hd : 0 ≤ d) (hdsq : d^2*(1+t^2)=1)
    (hb : scale S p*(d*M) ≤ N) : M^2 ≤ (N^2+N^2*t^2)*S := by
  have H := norm_sq_bound N (d*M) S p hN (mul_nonneg hd hM) hS hp hb
  calc
    M^2 = (d*M)^2*(1+t^2) := by
      rw [mul_pow]
      calc
        M^2 = (d^2*(1+t^2))*M^2 := by rw [hdsq,one_mul]
        _ = _ := by ring
    _ ≤ (N^2*S)*(1+t^2) := mul_le_mul_of_nonneg_right H (by positivity)
    _ = _ := by ring

theorem mixed_normalized_bound (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (W : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (hW : star (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ) = (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (ζ : unitary ℂ) (c t : ℝ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let B : Operator L q := liftLocal (X k) (kernel U e)
    let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    let u : State L q := Complex.I • asMap (L := L) (q := q)
      (orderedPrefix (Function.update A l C) n) ψ
    let w : State L q := ((ζ : ℂ)*Complex.I) • asMap (L := L) (q := q)
      (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ
    ‖(((scale (cost e (2/a k) (c*t)) (2/a k) * ReflectionRotation.scale t : ℝ) : ℂ) •
      (v + t • u + (c*t^2) • w))‖ ≤ ‖v‖ := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let B : Operator L q := liftLocal (X k) (kernel U e)
  let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let u : State L q := Complex.I • asMap (L := L) (q := q)
    (orderedPrefix (Function.update A l C) n) ψ
  let w : State L q := ((ζ : ℂ)*Complex.I) • asMap (L := L) (q := q)
    (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ
  let z : State L q := v+t • u+(c*t^2) • w
  let b := scale (cost e (2/a k) (c*t)) (2/a k)
  let d := ReflectionRotation.scale t
  let G : LocalPositiveFilter q (X k) :=
    ⟨normalized U e (2/a k) (c*t), normalized_posSemidef U e he (2/a k) (c*t)⟩
  have hG : filterTracePower G (2/a k) = 1 :=
    normalized_capacity U e he (2/a k) (by linarith) hs (c*t)
  let R : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ) := ReflectionRotation.rotation W hW t
  have hR : filterTracePower (rightPositive (F l) R) (2/a l) = 1 := by
    rw [rightPositive_capacity]
    exact hF.1 ⟨l,hl⟩
  have hb := two_replacement_bound hq X hX a ψ n F hF k l hk hl hkl
    (perturbUnitary U e ζ (c*t)) R G hG (rightPositive (F l) R) hR
  have hmat : liftLocal (X k)
      ((perturbUnitary U e ζ (c*t) : Matrix _ _ ℂ)*G.matrix) =
      (b : ℂ) • (A k + (((c*t : ℝ) : ℂ)*(ζ : ℂ)) • B) := by
    rw [show G.matrix = normalized U e (2/a k) (c*t) from rfl,
      normalized_factorization, ← hrep, liftLocal_smul, liftLocal_add, liftLocal_smul]
  have hmat' : liftLocal (X l) ((R : Matrix _ _ ℂ)*(rightPositive (F l) R).matrix) =
      (d : ℂ) • (A l + ((t : ℂ)*Complex.I) • C) := by
    rw [rightPositive_factorization]
    change liftLocal (X l) ((F l).matrix*((d : ℂ) •
      (1+((t : ℂ)*Complex.I) • (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ)))) = _
    simp only [mul_smul_comm,mul_add,mul_one,liftLocal_smul,liftLocal_add]
    rfl
  have hkzero : asMap (L := L) (q := q) (orderedPrefix (Function.update A k B) n) ψ = 0 :=
    kernel_output_zero hq X hX a ψ n F hF k hk hp U e he hrep hs
  have hout : asMap (L := L) (q := q) (orderedPrefix
      (Function.update (Function.update A k
        (liftLocal (X k) ((perturbUnitary U e ζ (c*t) : Matrix _ _ ℂ)*G.matrix))) l
        (liftLocal (X l) ((R : Matrix _ _ ℂ)*(rightPositive (F l) R).matrix))) n) ψ =
      ((b*d : ℝ) : ℂ) • z := by
    rw [hmat,hmat']
    exact two_affine_kernel_output A k l n hk hl hkl B C ψ hkzero ζ c t b d
  have hfv : filteredVector (fun j : Fin n => F j.val) ψ = v := by
    unfold filteredVector
    rw [PhysicalCurve.orderedFilterProduct_eq_prefix]
  rw [hout,hfv] at hb
  exact hb

theorem mixed_envelope (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (W : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (hW : star (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ) = (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (ζ : unitary ℂ) (c t : ℝ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let B : Operator L q := liftLocal (X k) (kernel U e)
    let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    let u : State L q := Complex.I • asMap (L := L) (q := q)
      (orderedPrefix (Function.update A l C) n) ψ
    let w : State L q := ((ζ : ℂ)*Complex.I) • asMap (L := L) (q := q)
      (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ
    ‖v + t • u + (c*t^2) • w‖^2 ≤
      (‖v‖^2+‖v‖^2*t^2)*cost e (2/a k) (c*t) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let B : Operator L q := liftLocal (X k) (kernel U e)
  let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let u : State L q := Complex.I • asMap (L := L) (q := q)
    (orderedPrefix (Function.update A l C) n) ψ
  let w : State L q := ((ζ : ℂ)*Complex.I) • asMap (L := L) (q := q)
    (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ
  let z : State L q := v+t • u+(c*t^2) • w
  let b := scale (cost e (2/a k) (c*t)) (2/a k)
  let d := ReflectionRotation.scale t
  have hb := mixed_normalized_bound hq X hX a ψ n F hF k l hk hl hkl hp U e he hrep hs W hW ζ c t
  change ‖((b*d : ℝ) : ℂ) • z‖ ≤ ‖v‖ at hb
  have hbpos : 0 < b := scale_pos _ _
    (lt_of_lt_of_le zero_lt_one (one_le_cost e (2/a k) (c*t)))
  have hdpos : 0 < d := ReflectionRotation.scale_pos t
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos hbpos hdpos)] at hb
  have hb' : b*(d*‖z‖) ≤ ‖v‖ := by simpa [mul_assoc] using hb
  exact mixed_scalar_bound ‖v‖ ‖z‖ (cost e (2/a k) (c*t)) (2/a k) d t
    (norm_nonneg _) (norm_nonneg _) (one_le_cost e (2/a k) (c*t)) hp hdpos.le
    (ReflectionRotation.scale_sq t) hb'

theorem mixed_transition_zero (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (W : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (hW : star (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ) = (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ)) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let B : Operator L q := liftLocal (X k) (kernel U e)
    let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    inner ℂ (asMap (L := L) (q := q) (orderedPrefix A n) ψ)
      (asMap (L := L) (q := q)
        (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ) = 0 := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let B : Operator L q := liftLocal (X k) (kernel U e)
  let C : Operator L q := liftLocal (X l) ((F l).matrix*(W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let u : State L q := Complex.I • asMap (L := L) (q := q)
    (orderedPrefix (Function.update A l C) n) ψ
  let w : State L q := asMap (L := L) (q := q)
    (orderedPrefix (Function.update (Function.update A k B) l C) n) ψ
  let K : ℝ := ∑ i, if e i = 0 then (1:ℝ) else 0
  have hzero (ζ : unitary ℂ) :
      (inner ℂ v (((ζ : ℂ)*Complex.I) • w)).re = 0 := by
    let : InnerProductSpace ℝ (State L q) := InnerProductSpace.rclikeToReal ℂ (State L q)
    have hb (c t : ℝ) : ‖v+t • u+(c*t^2) • (((ζ : ℂ)*Complex.I) • w)‖^2 ≤
        (‖v‖^2+‖v‖^2*t^2)*(1+K*|c*t|^(2/a k)) :=
      mixed_envelope hq X hX a ψ n F hF k l hk hl hkl hp U e he hrep hs W hW ζ c t
    exact OptimizerFlatDirection.mixed_direction_vanishes v u
      (((ζ : ℂ)*Complex.I) • w) K (2/a k) hp hb
  have hi := hzero 1
  let ζI : unitary ℂ := ⟨Complex.I, by
    constructor <;> simp [RCLike.star_def, Complex.I_mul_I]⟩
  have hr := hzero ζI
  change inner ℂ v w = 0
  apply Complex.ext
  · simpa [ζI,inner_smul_right] using hr
  · simpa [inner_smul_right] using hi

end PolynomialPEPS.Subvolume.ActualKernel

end

end OAI
