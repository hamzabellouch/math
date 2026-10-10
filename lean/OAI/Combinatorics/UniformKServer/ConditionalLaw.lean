import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                     
section

/-! Finite posterior calculus for the finite-law construction.  All conditional
 laws are computed from fiber weights, including the zero-probability fibers.
 This supplies, rather than assumes, the all-step filtering identities. -/
namespace UniformKServer.ConditionalLaw
noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
variable {Ω : Type*} [Fintype Ω]

def mass (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) : ℝ :=
  ∑ v, if F.r ω v then w v else 0

def kernel (w : Ω → ℝ) (F : Setoid Ω) (ω v : Ω) : ℝ :=
  if F.r ω v then w v / mass w F ω else 0

def posterior (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ v, kernel w F ω v * X v

def measurable (F : Setoid Ω) (X : Ω → ℝ) : Prop :=
  ∀ ω v, F.r ω v → X ω = X v

theorem mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω : Ω) :
    0 ≤ mass w F ω := sum_nonneg fun v _ => by
  split_ifs
  · exact hw v
  · exact le_rfl

theorem weight_le_mass {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω : Ω) :
    w ω ≤ mass w F ω := by
  have h := single_le_sum (f := fun v => if F.r ω v then w v else 0)
    (fun v (_ : v ∈ univ) => by split_ifs; exact hw v; exact le_rfl) (mem_univ ω)
  simpa only [mass,ite_eq_left (F.refl ω)] using h

theorem mass_eq (w : Ω → ℝ) (F : Setoid Ω) {ω v : Ω} (h : F.r ω v) :
    mass w F ω = mass w F v := by
  apply sum_congr rfl
  intro z _
  have he : F.r ω z ↔ F.r v z := ⟨fun h' => F.trans (F.symm h) h',fun h' => F.trans h h'⟩
  simp only [he]

theorem kernel_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (ω v : Ω) :
    0 ≤ kernel w F ω v := by
  unfold kernel
  split_ifs
  · exact div_nonneg (hw v) (mass_nonneg hw F ω)
  · rfl

theorem kernel_sum (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) :
    (∑ v, kernel w F ω v) = mass w F ω/mass w F ω := by
  calc
    _ = ∑ v, (if F.r ω v then w v else 0)/mass w F ω := by
      apply sum_congr rfl
      intro v _
      by_cases h : F.r ω v
      · simp only [kernel,ite_eq_left h]
      · simp only [kernel,ite_eq_right h,zero_div]
    _ = _ := by rw [←sum_div]; rfl

theorem balance (w : Ω → ℝ) (F : Setoid Ω) (ω v : Ω) :
    w ω*kernel w F ω v = w v*kernel w F v ω := by
  by_cases h : F.r ω v
  · simp only [kernel,ite_eq_left h,ite_eq_left (F.symm h),mass_eq w F h]
    ring
  · have h' : ¬F.r v ω := fun h' => h (F.symm h')
    simp only [kernel,ite_eq_right h,ite_eq_right h',mul_zero]

theorem weighted_kernel_sum {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω) (v : Ω) :
    (∑ ω, w ω*kernel w F ω v) = w v := by
  simp_rw [balance w F]
  rw [←mul_sum,kernel_sum]
  by_cases h : mass w F v = 0
  · have hz : w v = 0 := le_antisymm (by simpa only [h] using weight_le_mass hw F v) (hw v)
    simp only [hz,zero_mul]
  · rw [div_self h,mul_one]

theorem posterior_measurable (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ℝ) :
    measurable F (posterior w F X) := by
  intro ω v h
  apply sum_congr rfl
  intro z _
  have he : F.r ω z ↔ F.r v z := ⟨fun h' => F.trans (F.symm h) h',fun h' => F.trans h h'⟩
  simp only [kernel,he,mass_eq w F h]

/-- The finite conditional-expectation identity. The test function is old
 history measurable; no restriction to a later selected event is made. -/
theorem test_identity {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (a X : Ω → ℝ) (ha : measurable F a) :
    (∑ ω, w ω*a ω*posterior w F X ω) = ∑ ω, w ω*a ω*X ω := by
  simp only [posterior,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  have he (ω : Ω) : w ω*a ω*(kernel w F ω v*X v) =
      (a v*X v)*(w ω*kernel w F ω v) := by
    by_cases h : F.r ω v
    · rw [ha ω v h]; ring
    · simp only [kernel,ite_eq_right h,mul_zero,zero_mul]
  simp_rw [he]
  rw [←mul_sum,weighted_kernel_sum hw]
  ring

theorem filtering {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F G : Setoid Ω)
    (hGF : ∀ ω v, G.r ω v → F.r ω v) (a X : Ω → ℝ) (ha : measurable F a) :
    (∑ ω, w ω*a ω*(posterior w G X ω-posterior w F X ω)) = 0 := by
  simp only [mul_sub,sum_sub_distrib]
  rw [test_identity hw G a X (fun ω v h => ha ω v (hGF ω v h)),test_identity hw F a X ha,sub_self]

theorem posterior_nonneg {w X : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hX : ∀ ω, 0 ≤ X ω) (F : Setoid Ω) (ω : Ω) :
    0 ≤ posterior w F X ω := sum_nonneg fun v _ => mul_nonneg (kernel_nonneg hw F ω v) (hX v)

theorem posterior_le_one {w X : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hX : ∀ ω, X ω ≤ 1) (F : Setoid Ω) (ω : Ω) :
    posterior w F X ω ≤ 1 := by
  calc
    _ ≤ ∑ v, kernel w F ω v := sum_le_sum fun v _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hX v) (kernel_nonneg hw F ω v)
    _ ≤ 1 := by rw [kernel_sum]; exact div_self_le_one (mass w F ω)

theorem posterior_sub (w : Ω → ℝ) (F : Setoid Ω) (X Y : Ω → ℝ) (ω : Ω) :
    posterior w F (fun v => X v-Y v) ω = posterior w F X ω-posterior w F Y ω := by
  simp only [posterior,mul_sub,sum_sub_distrib]

theorem posterior_abs {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (X : Ω → ℝ) (ω : Ω) : |posterior w F X ω| ≤ posterior w F (fun v => |X v|) ω := by
  unfold posterior
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro v _
  rw [abs_mul,abs_of_nonneg (kernel_nonneg hw F ω v)]

theorem expected_contraction {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (X Y : Ω → ℝ) :
    (∑ ω, w ω*|posterior w F X ω-posterior w F Y ω|) ≤
      ∑ ω, w ω*|X ω-Y ω| := by
  calc
    _ ≤ ∑ ω, w ω*posterior w F (fun v => |X v-Y v|) ω := sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (by rw [←posterior_sub]; exact posterior_abs hw F _ ω) (hw ω)
    _ = _ := by
      simpa only [mul_one] using test_identity hw F (fun _ => 1) (fun v => |X v-Y v|) (by intro ω v _; rfl)

end
end UniformKServer.ConditionalLaw

end

end OAI
