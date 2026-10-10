import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalRellich
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedRicci.SobolevInterpolation

namespace OAI

/-! Global Smooth Compact. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)
lemma sobolev_interpolation (r s t : ℝ) (hst : s < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.embed s f‖ ≤ ε*‖D.embed t f‖+C*‖D.embed r f‖ := by
  obtain ⟨C,hC,hc⟩ := schwartz_sobolev_interpolation (E:=EC d) r s t hst hε
  refine ⟨C,hC,fun f => ?_⟩
  change ‖D.coordinates s f‖ ≤ ε*‖D.coordinates t f‖+C*‖D.coordinates r f‖
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro p
  exact (hc (localize A (D.index p) (D.weight p) (D.support_sub p) f)).trans
    (add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm (D.coordinates t f) p) hε.le)
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (D.coordinates r f) p) hC))

lemma cauchy_of_low (f : ℕ → Smooth A) (s t : ℝ) (hst : s < t)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖D.embed t (f n)‖ ≤ B)
    (hc : CauchySeq (fun n => D.embed 0 (f n))) :
    CauchySeq (fun n => D.embed s (f n)) := by
  obtain ⟨B,hB,hb⟩ := hbound
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let η := ε/(4*(B+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C,hC,hI⟩ := D.sobolev_interpolation 0 s t hst hη
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (ε/(4*(C+1))) (div_pos hε (by positivity))
  refine ⟨N,fun m hm n hn => ?_⟩
  have hhigh : ‖D.embed t (f m-f n)‖ ≤ 2*B := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by linarith [hb m,hb n])
  have hlow : ‖D.embed 0 (f m-f n)‖ < ε/(4*(C+1)) := by
    simpa only [map_sub,dist_eq_norm] using hN m hm n hn
  rw [dist_eq_norm,← map_sub]
  have h1 : η*(2*B) < ε/2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(B+1))).mpr
    nlinarith
  have h2 : C*(ε/(4*(C+1))) < ε/2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 4*(C+1))).mpr
    nlinarith
  calc
    _ ≤ η*‖D.embed t (f m-f n)‖+C*‖D.embed 0 (f m-f n)‖ := hI _
    _ ≤ η*(2*B)+C*(ε/(4*(C+1))) := add_le_add
      (mul_le_mul_of_nonneg_left hhigh hη.le) (mul_le_mul_of_nonneg_left hlow.le hC)
    _ < ε := by linarith
end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

theorem smooth_limit_of_all_bounds (f : ℕ → Smooth A)
    (hb : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖D.localizers.embed (k:ℝ) (f n)‖ ≤ B)
    (u : D.localizers.Sobolev 0)
    (hu : Tendsto (fun n => D.localizers.embed 0 (f n)) atTop (𝓝 u)) :
    ∃ F : Smooth A, ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (f n))
      atTop (𝓝 (D.localizers.embed (k:ℝ) F)) := by
  have hc (k : ℕ) : CauchySeq (fun n => D.localizers.embed (k:ℝ) (f n)) :=
    D.localizers.cauchy_of_low f (k:ℝ) ((k+1:ℕ):ℝ) (by exact_mod_cast Nat.lt_succ_self k)
      (hb (k+1)) hu.cauchySeq
  choose v hv using fun k => cauchySeq_tendsto_of_complete (hc k)
  have hlow (k : ℕ) : D.localizers.lower (k:ℝ) 0 (v k) = u := by
    have hh := ((D.localizers.lower (k:ℝ) 0).continuous.tendsto (v k)).comp (hv k)
    simp only [Function.comp_def,D.localizers.lower_embed (Nat.cast_nonneg k)] at hh
    exact tendsto_nhds_unique hh hu
  obtain ⟨F,hF⟩ := D.allRegular_smooth (show D.localizers.AllRegular u from fun k => ⟨v k,hlow k⟩)
  refine ⟨F,fun k => ?_⟩
  have he : v k = D.localizers.embed (k:ℝ) F := by
    apply D.localizers.lower_injective (Nat.cast_nonneg k)
    rw [hlow,D.localizers.lower_embed (Nat.cast_nonneg k),hF]
  exact he ▸ hv k

theorem smooth_subsequence (f : ℕ → Smooth A)
    (hb : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖D.localizers.embed (k:ℝ) (f n)‖ ≤ B) :
    ∃ F : Smooth A, ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ k : ℕ,
      Tendsto (fun n => D.localizers.embed (k:ℝ) (f (ν n))) atTop
        (𝓝 (D.localizers.embed (k:ℝ) F)) := by
  obtain ⟨B,hB,hb2⟩ := hb 2
  let K := closure (D.localizers.lower 2 0 '' Metric.closedBall 0 B)
  have hK : IsCompact K := D.lower_compact.isCompact_closure_image_closedBall B
  have hfK (n : ℕ) : D.localizers.embed 0 (f n) ∈ K := by
    apply subset_closure
    refine ⟨D.localizers.embed 2 (f n),?_,D.localizers.lower_embed (by norm_num) (f n)⟩
    simpa only [Metric.mem_closedBall,dist_zero_right,Nat.cast_ofNat] using hb2 n
  obtain ⟨u,_,ν,hν,hu⟩ := hK.tendsto_subseq hfK
  obtain ⟨F,hF⟩ := D.smooth_limit_of_all_bounds (f ∘ ν)
    (fun k => by obtain ⟨B,hB,hb⟩ := hb k; exact ⟨B,hB,fun n => hb (ν n)⟩) u hu
  exact ⟨F,ν,hν,hF⟩
end GluingData
end GlobalElliptic

end
end

end OAI
