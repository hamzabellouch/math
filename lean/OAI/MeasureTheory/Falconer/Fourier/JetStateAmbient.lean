import OAI.MeasureTheory.Falconer.Fourier.JetStateOperations
import OAI.MeasureTheory.Falconer.Fourier.UniformJetBudget
import OAI.MeasureTheory.Falconer.Angular.SphereProduct

namespace OAI

/-! # Ambient representatives of the exact recursive symbols

The bound is uniform in the descriptor list and scale. It retains the
ambient representative needed for the full-sphere far expansion.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem iteratedFDeriv_mul_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {B C D E : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (t : ℕ) (x : V)
    (hb : ∀ j ≤ t, ‖iteratedFDeriv ℝ j f x‖ ≤ B*D^j)
    (hc : ∀ j ≤ t, ‖iteratedFDeriv ℝ j g x‖ ≤ C*E^j) :
    ‖iteratedFDeriv ℝ t (fun x => f x*g x) x‖ ≤ (B*C)*(D+E)^t := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (by simp : (t : ℕ∞ω) ≤ ∞)
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*(B*D^j)*(C*E^(t-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb j hjt) (Nat.cast_nonneg _))
        (hc (t-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (pow_nonneg hD _)))
    _ = (B*C)*(∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*D^j*E^(t-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (B*C)*(D+E)^t := by
      congr 1
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring


namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {Dq : ℝ}

noncomputable def ambient (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x z : Space (n+2)) : ℂ :=
  f.spatial x*(A⁻¹:ℝ)*
    ((∏ b ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z : ℝ)*f.angular z)

 theorem ambient_sphere (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) (w : Sphere (n+2)) :
    f.ambient Q ρ m N σ J i S A x w = f.value Q ρ m N σ J i S A x w := by
  simp only [ambient,value,multiplier,Complex.ofReal_prod,
    normalizedAmbientDescriptorJet_sphere,descriptorJetProduct,id_eq]
  ring

 theorem ambient_smooth (f : DescriptorJetSymbol n K L F Dq)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (x : Space (n+2)) :
    ContDiff ℝ ∞ (f.ambient Q ρ m N σ J i S A x) := by
  apply contDiff_const.mul
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_prod (fun b _ =>
    normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x))).mul f.angular_smooth

end DescriptorJetSymbol

 theorem exists_descriptorJetSymbol_ambient_budget (n K L : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol n K L F Dq) (x : Space (n+2)) (t : ℕ), t ≤ L →
      ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (f.ambient Q ρ m N σ J i S A x) w‖ ≤
          (B^K*A⁻¹)*(E+Dq)^t := by
  classical
  obtain ⟨B,hB,hjet⟩ := normalizedAmbientJetProduct_uniform_budget (n+2) K L
  refine ⟨B,hB,?_⟩
  intro F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x t ht w
  let P : Space (n+2) → ℝ := fun z => ∏ b ∈ F,
    normalizedAmbientDescriptorJet Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z
  have hP : ContDiff ℝ ∞ P := contDiff_prod (fun b _ =>
    normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x)
  have hPc : ContDiff ℝ ∞ (fun z => (P z : ℂ)) := Complex.ofRealCLM.contDiff.comp hP
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ (F.card:ℝ)*B*Dmask).trans hE
  have hp (j : ℕ) (hj : j ≤ t) :
      ‖iteratedFDeriv ℝ j (fun z => (P z : ℂ)) w‖ ≤ B^K*E^j := by
    have he := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (hP.contDiffAt (x := (w:Space (n+2)))) (by simp : (j:ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ P) w‖ ≤ _
    rw [he]
    exact (hjet Q ρ m N σ J i F id S (fun b => (f.jet b).order)
      (fun b => (f.jet b).vectors) hsep f.order_le (fun b _ => (f.jet b).norm_vectors)
      Dmask hDm hscale x w j (hj.trans ht)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hE j) (by positivity))
  have hpq := iteratedFDeriv_mul_bound (fun z => (P z : ℂ)) f.angular hPc f.angular_smooth
    (by positivity : 0 ≤ B^K) (by norm_num : (0:ℝ) ≤ 1) hE0 hDq t (w:Space (n+2)) hp
    (fun j hj => by simpa only [one_mul] using f.angular_derivative j (hj.trans ht) w)
  have hq : ContDiff ℝ ∞ (fun z => (P z : ℂ)*f.angular z) := hPc.mul f.angular_smooth
  change ‖iteratedFDeriv ℝ t (fun z => (f.spatial x*(A⁻¹:ℝ)) •
    ((P z : ℂ)*f.angular z)) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hq.of_le (by simp)).contDiffAt,norm_smul]
  have hs : ‖f.spatial x*(A⁻¹:ℝ)‖ ≤ A⁻¹ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hA)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_pos.mpr hA).le
  apply (mul_le_mul hs hpq (norm_nonneg _) (inv_pos.mpr hA).le).trans_eq
  ring

end Falconer

end OAI
