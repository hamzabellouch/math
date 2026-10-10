import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid
import OAI.MeasureTheory.FalconerCompletion.Recursion.ExistsFarSeparationPower2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff Topology

lemma inner_normalized_of_close {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {c u : V} (hc : 0<‖c‖) (hu : ‖u-c‖≤‖c‖/2) :
    (1/3:ℝ)≤ inner ℝ (‖u‖⁻¹ • u) (‖c‖⁻¹ • c) := by
  have ht : ‖u‖≤‖u-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (u-c) c
  have ht' : ‖c‖≤‖u-c‖+‖u‖ := by
    simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (c-u) u
  have hp : 0<‖u‖ := by linarith
  have hi := (abs_le.mp (abs_real_inner_le_norm (u-c) c)).1
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hi
  have hi' : ‖c‖^2/2≤ inner ℝ u c := by nlinarith
  rw [real_inner_smul_left,real_inner_smul_right]
  have h : (1/3:ℝ)*(‖u‖*‖c‖)≤ inner ℝ u c := by nlinarith
  apply (le_div_iff₀ (mul_pos hp hc)).mpr at h
  simpa only [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm] using h

variable {d : ℕ}

noncomputable def separatedAxis (a : ℕ) (X Y : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  radialVector (Attempt4FullFar.ambientGridCenter a X) (Attempt4FullFar.ambientGridCenter a Y)

noncomputable def separatedCutoff (a : ℕ) (X Y : Fin d → ℤ) (w : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Real.smoothTransition (4*inner ℝ w (separatedAxis a X Y)+1/2)

lemma separatedCutoff_contDiff (a : ℕ) (X Y : Fin d → ℤ) :
    ContDiff ℝ ∞ (separatedCutoff a X Y) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add contDiff_const))

lemma separatedCutoff_norm_le (a : ℕ) (X Y : Fin d → ℤ) (w : EuclideanSpace ℝ (Fin d)) :
    ‖separatedCutoff a X Y w‖≤1 := by
  rw [separatedCutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma separated_direction_inner {a : ℕ} {K : ℝ} (hK : 32*(d+1:ℝ)≤K)
    {X Y : Fin d → ℤ} (hs : farSeparatedGridND a K X Y)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈Attempt4FullFar.ambientGridCell a X) (hy : y∈Attempt4FullFar.ambientGridCell a Y) :
    (1/3:ℝ)≤ inner ℝ (radialVector x y) (separatedAxis a X Y) := by
  have hp : 0<(2:ℝ)^a := by positivity
  have hKp : 0<K := by have hd : (0:ℝ)≤d := Nat.cast_nonneg d; linarith
  have hc : 0<‖Attempt4FullFar.ambientGridCenter a X-Attempt4FullFar.ambientGridCenter a Y‖ :=
    (div_pos hKp (mul_pos (by norm_num) hp)).trans_le hs.1
  have hcx := Attempt4FullFar.ambientGridCell_dist_le hx (Attempt4FullFar.ambientGridCenter_mem a X)
  have hcy := Attempt4FullFar.ambientGridCell_dist_le hy (Attempt4FullFar.ambientGridCenter_mem a Y)
  have he : (x-y)-(Attempt4FullFar.ambientGridCenter a X-Attempt4FullFar.ambientGridCenter a Y)=
      (x-Attempt4FullFar.ambientGridCenter a X)-(y-Attempt4FullFar.ambientGridCenter a Y) := by abel
  have hb := norm_sub_le (x-Attempt4FullFar.ambientGridCenter a X) (y-Attempt4FullFar.ambientGridCenter a Y)
  have hk := div_le_div_of_nonneg_right hK hp.le
  have hlo := hs.1
  have heq : K/(8*(2:ℝ)^a)=(K/(2:ℝ)^a)/8 := by ring
  rw [heq,dist_eq_norm] at hlo
  have hk' : 32*((d+1:ℝ)/(2:ℝ)^a)≤K/(2:ℝ)^a := by simpa only [mul_div_assoc] using hk
  rw [dist_eq_norm,norm_sub_rev] at hcx hcy
  apply inner_normalized_of_close hc
  rw [he]
  linarith

lemma separatedCutoff_local {a : ℕ} {K : ℝ} (hK : 32*(d+1:ℝ)≤K)
    {X Y : Fin d → ℤ} (hs : farSeparatedGridND a K X Y)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈Attempt4FullFar.ambientGridCell a X) (hy : y∈Attempt4FullFar.ambientGridCell a Y) :
    separatedCutoff a X Y =ᶠ[𝓝 (radialVector x y)] (fun _ => 1) ∧
    separatedCutoff a X Y =ᶠ[𝓝 (-(radialVector x y))] (fun _ => 0) := by
  have hi := separated_direction_inner hK hs hx hy
  have hf : Continuous (fun w : EuclideanSpace ℝ (Fin d) => inner ℝ w (separatedAxis a X Y)) :=
    continuous_id.inner continuous_const
  constructor
  · have hh : ∀ᶠ w in 𝓝 (radialVector x y), (1/4:ℝ)< inner ℝ w (separatedAxis a X Y) :=
      hf.continuousAt.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hh] with w hw
    rw [separatedCutoff,Real.smoothTransition.one_of_one_le (by linarith),Complex.ofReal_one]
  · have hh : ∀ᶠ w in 𝓝 (-(radialVector x y)), inner ℝ w (separatedAxis a X Y)< -(1/4:ℝ) :=
      hf.continuousAt.eventually (Iio_mem_nhds (by simp only [inner_neg_left]; linarith))
    filter_upwards [hh] with w hw
    rw [separatedCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),Complex.ofReal_zero]

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

noncomputable def gridOffsetVector (Z : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => (Z j:ℝ))

lemma grid_centers_sub (a : ℕ) (X Y : Fin d → ℤ) :
    Attempt4FullFar.ambientGridCenter a X-Attempt4FullFar.ambientGridCenter a Y=
      ((2:ℝ)^a)⁻¹ • gridOffsetVector (X-Y) := by
  ext j
  change ((X j:ℝ)+1/2)/(2:ℝ)^a-((Y j:ℝ)+1/2)/(2:ℝ)^a=
    ((2:ℝ)^a)⁻¹*((X j-Y j:ℤ):ℝ)
  rw [Int.cast_sub]
  ring

lemma normalized_pos_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {r : ℝ} (hr : 0<r) (v : V) :
    ‖r • v‖⁻¹ • (r • v)=‖v‖⁻¹ • v := by
  simp [norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_smul,mul_inv_rev,hr.ne']

lemma separatedAxis_offset (a : ℕ) (X Y : Fin d → ℤ) :
    separatedAxis a X Y=‖gridOffsetVector (X-Y)‖⁻¹ • gridOffsetVector (X-Y) := by
  unfold separatedAxis radialVector
  rw [grid_centers_sub,normalized_pos_smul (by positivity : 0<((2:ℝ)^a)⁻¹)]

lemma separatedCutoff_offset (a : ℕ) (X Y : Fin d → ℤ) :
    separatedCutoff a X Y=separatedCutoff 0 (X-Y) 0 := by
  funext w
  simp only [separatedCutoff,separatedAxis_offset,sub_zero]

noncomputable def separatedOffsets (K : ℝ) : Set (Fin d → ℤ) :=
  {Z | ∀ j, Z j∈Icc (-⌈4*K⌉) ⌈4*K⌉}

lemma separatedOffsets_finite (K : ℝ) : (separatedOffsets (d:=d) K).Finite :=
  Set.Finite.pi' (fun _ => Set.finite_Icc _ _)

lemma gridOffset_mem {a : ℕ} {K : ℝ} {X Y : Fin d → ℤ}
    (hs : Attempt4FullFar.farSeparatedGridND a K X Y) : X-Y∈separatedOffsets K := by
  intro j
  have h := Attempt4FullFar.ambientGridCenter_coordinate_bound hs.2 j
  have he : (X j:ℝ)+1/2-(2:ℝ)^a*Attempt4FullFar.ambientGridCenter a Y j=(X j-Y j:ℝ) := by
    rw [Attempt4FullFar.ambientGridCenter_apply]
    field_simp
    ring
  have he' : (2:ℝ)^a*(4*K/(2:ℝ)^a)=4*K := by field_simp
  rw [he,he'] at h
  have hc := Int.le_ceil (4*K)
  have hlo : -(⌈4*K⌉:ℤ)≤X j-Y j := by
    have hh : -((⌈4*K⌉:ℤ):ℝ)≤(X j-Y j:ℝ) := by linarith [abs_le.mp h]
    exact_mod_cast hh
  have hhi : X j-Y j≤(⌈4*K⌉:ℤ) := by
    have hh : (X j-Y j:ℝ)≤((⌈4*K⌉:ℤ):ℝ) := by linarith [abs_le.mp h]
    exact_mod_cast hh
  exact ⟨hlo,hhi⟩

lemma eventually_all_separated_cutoffs (K : ℝ)
    (P : (EuclideanSpace ℝ (Fin d) → ℂ) → ℕ → Prop)
    (hP : ∀ Z∈separatedOffsets K, ∀ᶠ N : ℕ in Filter.atTop, P (separatedCutoff 0 Z 0) N) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (a : ℕ) (X Y : Fin d → ℤ),
      Attempt4FullFar.farSeparatedGridND a K X Y → P (separatedCutoff a X Y) N := by
  have h := (Filter.eventually_all_finite (separatedOffsets_finite K)).mpr hP
  filter_upwards [h] with N hN
  intro a X Y hs
  rw [separatedCutoff_offset]
  exact hN (X-Y) (gridOffset_mem hs)

lemma uniform_separatedCutoff_derivatives (K : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0≤C m) ∧ ∀ (a : ℕ) (X Y : Fin d → ℤ),
      Attempt4FullFar.farSeparatedGridND a K X Y → ∀ (m : ℕ) (w : EuclideanSpace ℝ (Fin d)),
      ‖w‖=1 → ‖iteratedFDeriv ℝ m (separatedCutoff a X Y) w‖≤C m := by
  classical
  have hm (m : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (a : ℕ) (X Y : Fin d → ℤ),
      Attempt4FullFar.farSeparatedGridND a K X Y → ∀ (w : EuclideanSpace ℝ (Fin d)),
      ‖w‖=1 → ‖iteratedFDeriv ℝ m (separatedCutoff a X Y) w‖≤C := by
    have hz (Z : Fin d → ℤ) : ∃ B : ℝ, 0≤B ∧ ∀ (w : EuclideanSpace ℝ (Fin d)),
        ‖w‖=1 → ‖iteratedFDeriv ℝ m (separatedCutoff 0 Z 0) w‖≤B := by
      have hf := (ContDiff.continuous_iteratedFDeriv (m:=m) (n:=∞) (by exact_mod_cast (le_top : (m:ℕ∞)≤⊤))
        (separatedCutoff_contDiff 0 Z 0)).norm
      obtain ⟨B,hB,hb⟩ := (bddAbove_iff_exists_ge (0:ℝ)).mp
        ((isCompact_sphere (0:EuclideanSpace ℝ (Fin d)) 1).bddAbove_image hf.continuousOn)
      refine ⟨B,hB,?_⟩
      intro w hw
      exact hb _ ⟨w,by simpa [Metric.mem_sphere] using hw,rfl⟩
    choose B hB hb using hz
    obtain ⟨C,hC,hc⟩ := (bddAbove_iff_exists_ge (0:ℝ)).mp
      (((separatedOffsets_finite (d:=d) K).image B).bddAbove)
    refine ⟨C,hC,?_⟩
    intro a X Y hs w hw
    rw [separatedCutoff_offset]
    exact (hb (X-Y) w hw).trans (hc _ ⟨X-Y,gridOffset_mem hs,rfl⟩)
  choose C hC hbound using hm
  exact ⟨C,hC,fun a X Y hs m w hw => hbound m a X Y hs w hw⟩

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
