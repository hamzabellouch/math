import OAI.MeasureTheory.Falconer.Estimates.GlobalDescriptorBounds
import OAI.MeasureTheory.Falconer.Measures.DescriptorProduct

namespace OAI

/-! # Normalized mask derivatives at reached anchors

Reached masks agree as ambient functions throughout a child cell. All their
ambient jets therefore agree too. Radius normalization makes each fixed
order uniformly bounded before any scale or descriptor is selected.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff

theorem descriptorAmbientMask_reached_eq {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (X : List (Fin d → Bool))
    (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) :
    descriptorAmbientMask Q ρ m N σ J i b S x =
      descriptorAmbientMask Q ρ m N σ J i b S (Q.descendant X).center := by
  let p := X.take (descriptorAnchor b)
  let q := X.drop (descriptorAnchor b)
  have hp : p.length = descriptorAnchor b := by
    simp only [p,List.length_take,Nat.min_eq_left hb]
  have hprefix (y : Space d) (hy : y ∈ (Q.descendant X).carrier) :
      y ∈ (Q.descendant p).carrier := by
    have he : X = p++q := (List.take_append_drop _ _).symm
    rw [he,Q.descendant_append] at hy
    exact (Q.descendant p).descendant_subset q hy
  funext z
  rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp (hprefix x hx),
    descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp
      (hprefix _ ((Q.descendant X).center_mem (Q.descendant_side_pos hQ X)))]

noncomputable def normalizedDescriptorJet {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (x : Space d) (w : Sphere d) : ℂ :=
  ((descriptorMaskRadius N σ b)^k *
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w) v : ℝ)

theorem normalizedDescriptorJet_reached {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (X : List (Fin d → Bool)) (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      normalizedDescriptorJet Q ρ m N σ J i b S k v (Q.descendant X).center w := by
  unfold normalizedDescriptorJet
  rw [descriptorAmbientMask_reached_eq Q hQ ρ m N σ J i b S X hb hx]


theorem normalizedDescriptorJet_zero {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (v : Fin 0 → Space d)
    (x : Space d) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S 0 v x w =
      (descriptorMask Q ρ m N σ J i b S x w : ℂ) := by
  simp only [normalizedDescriptorJet,pow_zero,iteratedFDeriv_zero_apply,one_mul]
  rfl

theorem normalizedDescriptorJet_support {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (x : Space d) (w : Sphere d)
    (h : normalizedDescriptorJet Q ρ m N σ J i b S k v x w ≠ 0) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  have hn : iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x)
      (w : Space d) ≠ 0 := by
    intro hz
    apply h
    simp only [normalizedDescriptorJet,hz,zero_apply,mul_zero,
      Complex.ofReal_zero]
  exact descriptorAmbientMask_tsupport_good Q ρ m N σ J i b S x w
    (support_iteratedFDeriv_subset (𝕜 := ℝ) k hn)

theorem normalizedDescriptorJet_bound (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x : Space d) (w : Sphere d), ‖normalizedDescriptorJet Q ρ m N σ J i b S k v x w‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientMask_global_derivatives d k
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x w
  have hr : 0 < descriptorMaskRadius N σ b := descriptorMaskRadius_pos N σ b
  have hprod : (∏ j, ‖v j‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => norm_nonneg (v j)) (fun j _ => hv j)
  have heval := (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w).le_opNorm v
  have he : |(iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w) v| ≤
      C*((descriptorMaskRadius N σ b)⁻¹)^k := by
    have hh := heval.trans (mul_le_of_le_one_right (norm_nonneg _) hprod)
    exact hh.trans (hbound Q ρ m N σ J i b S hsep x w)
  rw [normalizedDescriptorJet,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (pow_nonneg hr.le k)]
  calc
    _ ≤ (descriptorMaskRadius N σ b)^k*(C*((descriptorMaskRadius N σ b)⁻¹)^k) :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hr.le k)
    _ = C := by
      calc
        _ = C*((descriptorMaskRadius N σ b)*((descriptorMaskRadius N σ b)⁻¹))^k := by
          rw [mul_pow]
          ring
        _ = C := by rw [mul_inv_cancel₀ hr.ne',one_pow,mul_one]

end Falconer

end OAI
