import OAI.MeasureTheory.Falconer.Radial.VanishingSlabs
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Uniform small mass for bounded families of null affine hyperplanes -/

namespace Falconer
open Set Metric MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

private theorem finite_positive_minorant {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ I, r ≤ f i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a I ha ih =>
    obtain ⟨r,hr,hrI⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min r (f a),lt_min hr (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hrI i hi)

theorem uniform_bounded_affine_slabs {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {M B : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ, μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : Space d, ‖w‖ = 1 → ∀ a ∈ Icc (-B) B,
      μ {x | |inner ℝ w x-a| ≤ r} < η := by
  classical
  let K : Set (Space d × ℝ) := sphere 0 1 ×ˢ Icc (-B) B
  have hK : IsCompact K := (isCompact_sphere (0 : Space d) 1).prod isCompact_Icc
  have hsmall : ∀ p : K, ∃ r : ℝ, 0 < r ∧ μ {x | |inner ℝ p.val.1 x-p.val.2| ≤ r} < η := by
    intro p
    apply exists_small_affine_slab μ p.val.1 p.val.2 (hzero p.val.1 ?_ p.val.2) hη
    simpa only [mem_sphere,dist_zero_right] using p.property.1
  choose r hr hsmall using hsmall
  let U : K → Set (Space d × ℝ) := fun p => ball p.val (r p/(2*(M+1)))
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) (by
    intro p hp
    have hrp : 0 < r ⟨p,hp⟩/(2*(M+1)) := div_pos (hr ⟨p,hp⟩) (by positivity)
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self hrp⟩)
  obtain ⟨ρ,hρ,hρI⟩ := finite_positive_minorant I (fun p => r p/2)
    (fun p _ => half_pos (hr p))
  refine ⟨ρ,hρ,?_⟩
  intro w hw a ha
  have hpK : (w,a) ∈ K := ⟨by simpa only [mem_sphere,dist_zero_right] using hw,ha⟩
  obtain ⟨p,hp,hclose⟩ := mem_iUnion₂.mp (hI hpK)
  have hdist : dist (w,a) p.val < r p/(2*(M+1)) := hclose
  have hnear : (M+1)*dist (w,a) p.val ≤ r p/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(M+1))).mp hdist
    nlinarith only [hh]
  have hmono : ∀ᵐ x ∂μ, x ∈ {x | |inner ℝ w x-a| ≤ ρ} →
      x ∈ {x | |inner ℝ p.val.1 x-p.val.2| ≤ r p} := by
    filter_upwards [hbounded] with x hx
    intro hxr
    have hdiff := affine_slab_parameter_bound (w := p.val.1) (w' := w)
      (a := p.val.2) (a' := a) hx
    have hw' : ‖p.val.1-w‖ ≤ dist (w,a) p.val := by
      calc
        ‖p.val.1-w‖ = dist w p.val.1 := by rw [dist_eq_norm,norm_sub_rev]
        _ ≤ max (dist w p.val.1) (dist a p.val.2) := le_max_left _ _
        _ = dist (w,a) p.val := rfl
    have ha' : |p.val.2-a| ≤ dist (w,a) p.val := by
      simpa only [Prod.dist_eq,Real.dist_eq,abs_sub_comm] using
        (le_max_right (dist w p.val.1) (dist a p.val.2))
    have hdiff' : |(inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a)| ≤ r p/2 :=
      hdiff.trans ((add_le_add (mul_le_mul_of_nonneg_left hw' hM) ha').trans
        (by nlinarith only [hnear]))
    have habs : |inner ℝ p.val.1 x-p.val.2| ≤ |inner ℝ w x-a|+
        |(inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a)| := by
      calc
        _ = |(inner ℝ w x-a)+((inner ℝ p.val.1 x-p.val.2)-(inner ℝ w x-a))| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    have hrp := hρI p hp
    change |inner ℝ p.val.1 x-p.val.2| ≤ r p
    change |inner ℝ w x-a| ≤ ρ at hxr
    linarith only [habs,hdiff',hxr,hrp]
  exact (measure_mono_ae hmono).trans_lt (hsmall p)

end Falconer

end OAI
