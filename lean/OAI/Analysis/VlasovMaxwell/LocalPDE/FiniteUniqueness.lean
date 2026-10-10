import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma particle_difference_direction_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (hs₁ : ClassicalBefore d s₁ H) (hs₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x v : Vec) :
    fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hd₁ := particle_differentiableAt_positive hs₁.1 ht x v
  have hd₂ := particle_differentiableAt_positive hs₂.1 ht x v
  have hsp₁ : DifferentiableAt ℝ (particleBySpacetime s₁.f) ((t,x),v) :=
    (hd₁.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have hsp₂ : DifferentiableAt ℝ (particleBySpacetime s₂.f) ((t,x),v) :=
    (hd₂.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have he₁ := particle_spacetime_vlasov_before hs₁.1 hs₁.2.2.2.2.2.2.2.1 ht hth x v
  have he₂ := particle_spacetime_vlasov_before hs₂.1 hs₂.2.2.2.2.2.2.2.1 ht hth x v
  change fderiv ℝ (fun z => ((particleBySpacetime s₁.f-particleBySpacetime s₂.f) z)^2/2)
     ((t,x),v) _ = _
  rw [fderiv_square_half (hsp₁.sub hsp₂), fderiv_sub hsp₁ hsp₂]
  simp only [sub_apply,Pi.sub_apply,he₁,zero_sub]
  have hcross : cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)) =
      cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hcross]
  have hh : (((1:ℝ),velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      ((1,velocity v),s₂.E (t,x)+cross (velocity v) (s₂.B (t,x))) +
        ((0,0),(s₁.E (t,x)-s₂.E (t,x))+(cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)))) := by
    apply Prod.ext
    · simp
    · dsimp
      abel
  rw [hh,map_add,he₂,zero_add]
  have hv := fderiv_velocity_slice hsp₂
  change ∀ b, fderiv ℝ (fun v => s₂.f (t,x,v)) v b =
    fderiv ℝ (particleBySpacetime s₂.f) ((t,x),v) ((0,0),b) at hv
  rw [← hv]
  simp only [particleBySpacetime]
  ring

lemma squareDifference_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    RegularParticle (squareDifference s₁ s₂) := by
  refine ⟨((h₁.1.sub h₂.1).pow 2).div_const 2,?_⟩
  intro T hT
  obtain ⟨K₁,hK₁,hz₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hz₂⟩ := h₂.regularParticle.2 T hT
  refine ⟨K₁ ∪ K₂,hK₁.union hK₂,?_⟩
  intro t ht
  apply closure_minimal ?_ (hK₁.union hK₂).isClosed
  intro z hz
  by_contra hn
  have hf₁ : s₁.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₁.f (t,z))
    (fun hh => hn (Or.inl (hz₁ t ht hh)))
  have hf₂ : s₂.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₂.f (t,z))
    (fun hh => hn (Or.inr (hz₂ t ht hh)))
  exact hz (by simp [squareDifference,hf₁,hf₂])

lemma particle_difference_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (r,x)) t +
      divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hf := squareDifference_regular_before h₁ h₂
  obtain ⟨U,K,hU,hK,hp,hF,hz⟩ := hf.local_data ht x
  have he := particle_number_balance_param (s₁.E (t,x)) (s₁.B (t,x)) hU hK hp hF hz
  have he' : (∫ v : Vec, fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x)))) = _ :=
    integral_congr_ae (Filter.Eventually.of_forall (particle_difference_direction_before h₁ h₂ ht hth x))
  rw [he'] at he
  have hn := (hf.moment_regular (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  rw [deriv_time_slice (hn.differentiableAt (by simp))]
  apply Eq.trans ?_ he
  congr 1
  · congr 2
    ext p
    exact particleMoment_one _ p
  · apply Finset.sum_congr rfl
    intro i _
    have hflux := (hf.moment_regular contDiff_velocity).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
    have hc : DifferentiableAt ℝ (fun p => particleMoment (squareDifference s₁ s₂) velocity p i) (t,x) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
        (hflux.differentiableAt (by simp))
    rw [spatialPartial_time_slice hc]
    have heq : (fun p : ℝ × Vec => particleMoment (squareDifference s₁ s₂) velocity p i) =ᶠ[nhds (t,x)]
        (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (squareDifference s₁ s₂) (p,v)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
      exact hf.moment_component (contDiff_velocity (k := 1)).continuous hp.le p.2 i
    rw [heq.fderiv_eq (𝕜 := ℝ)]

lemma difference_maxwell_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => (‖s₁.E (r,x)-s₂.E (r,x)‖^2+‖s₁.B (r,x)-s₂.B (r,x)‖^2)/2) t +
      divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x =
        -dot (s₁.E (t,x)-s₂.E (t,x))
          (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
  have hE₁ := field_differentiableAt_positive h₁.2.1 ht x
  have hB₁ := field_differentiableAt_positive h₁.2.2.1 ht x
  have hE₂ := field_differentiableAt_positive h₂.2.1 ht x
  have hB₂ := field_differentiableAt_positive h₂.2.2.1 ht x
  have hE₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.E (r,x)) t := hE₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.B (r,x)) t := hB₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.E (r,x)) t := hE₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.B (r,x)) t := hB₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₁x : DifferentiableAt ℝ (fun y : Vec => s₁.E (t,y)) x := hE₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₁x : DifferentiableAt ℝ (fun y : Vec => s₁.B (t,y)) x := hB₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hE₂x : DifferentiableAt ℝ (fun y : Vec => s₂.E (t,y)) x := hE₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₂x : DifferentiableAt ℝ (fun y : Vec => s₂.B (t,y)) x := hB₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have he₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le hth).2.1 x
  have hb₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le hth).2.2.1 x
  have he₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le hth).2.1 x
  have hb₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le hth).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he₁ hb₁ he₂ hb₂
  apply maxwell_energy_balance (E := s₁.E-s₂.E) (B := s₁.B-s₂.B) (hE₁.sub hE₂) (hB₁.sub hB₂)
  · change deriv ((fun r => s₁.E (r,x))-(fun r => s₂.E (r,x))) t -
      curl ((fun y => s₁.B (t,y))-(fun y => s₂.B (t,y))) x = _
    rw [deriv_sub hE₁t hE₂t,curl_sub hB₁x hB₂x]
    calc
      _ = (deriv (fun r => s₁.E (r,x)) t-curl (fun y => s₁.B (t,y)) x)-
        (deriv (fun r => s₂.E (r,x)) t-curl (fun y => s₂.B (t,y)) x) := by abel
      _ = _ := by rw [he₁,he₂]; abel
  · change deriv ((fun r => s₁.B (r,x))-(fun r => s₂.B (r,x))) t +
      curl ((fun y => s₁.E (t,y))-(fun y => s₂.E (t,y))) x = _
    rw [deriv_sub hB₁t hB₂t,curl_sub hE₁x hE₂x]
    calc
      _ = (deriv (fun r => s₁.B (r,x)) t+curl (fun y => s₁.E (t,y)) x)-
        (deriv (fun r => s₂.B (r,x)) t+curl (fun y => s₂.E (t,y)) x) := by abel
      _ = _ := by rw [hb₁,hb₂]; simp

lemma differenceEnergy_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    ContDiffOn ℝ 1 (differenceEnergy s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((he.norm_sq ℝ).add (hb.norm_sq ℝ)).div_const 2 |>.add
    ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_const)

lemma differenceFlux_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    ContDiffOn ℝ 1 (differenceFlux s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (he.prodMk hb)
    (fun _ _ => mem_univ _)).add
      ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_velocity)

lemma differenceEnergy_continuous_slab_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (differenceEnergy s₁ s₂) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.continuousOn.sub h₂.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  have hb := (h₁.2.2.1.continuousOn.sub h₂.2.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  exact ((he.norm.pow 2).add (hb.norm.pow 2)).div_const 2 |>.add
    ((squareDifference_regular_before h₁ h₂).moment_continuous_slab continuous_const hT)

lemma differenceEnergy_integrable_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => differenceEnergy s₁ s₂ (t,x)) := by
  exact (((h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht).add
    ((h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht)).div_const 2 |>.add
      ((squareDifference_regular_before h₁ h₂).spatial_moment_integrable continuous_const ht)

lemma differenceEnergy_integrated_continuous_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, differenceEnergy s₁ s₂ (t,x)) (Icc 0 T) := by
  have he := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hb := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hp := (squareDifference_regular_before h₁ h₂).integrated_moment_continuous
    (w := fun _ => (1:ℝ)) continuous_const hT
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) = _
  have hiE := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht.1
  have hiB := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht.1
  have hiP := (squareDifference_regular_before h₁ h₂).spatial_moment_integrable
    (w := fun _ => (1:ℝ)) continuous_const ht.1
  calc
    _ = (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2)+
      (∫ x : Vec, particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) :=
        integral_add ((hiE.add hiB).div_const 2) hiP
    _ = _ := by rw [integral_div,integral_add hiE hiB]; rfl

lemma differenceFlux_bound_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖differenceFlux s₁ s₂ (t,x)‖ ≤ differenceEnergy s₁ s₂ (t,x) := by
  apply (norm_add_le _ _).trans
  apply add_le_add ?_ ((squareDifference_regular_before h₁ h₂).velocity_flux_bound ht x
    (fun v => squareDifference_nonneg _ _ _))
  apply (norm_cross_le _ _).trans
  dsimp [differenceFieldEnergy]
  nlinarith [sq_nonneg (‖s₁.E (t,x)-s₂.E (t,x)‖-‖s₁.B (t,x)-s₂.B (t,x)‖)]

lemma differenceEnergy_initial_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) (x : Vec) :
    differenceEnergy s₁ s₂ (0,x) = 0 := by
  have hf (v : Vec) : squareDifference s₁ s₂ (0,x,v)=0 := by
    rw [squareDifference_zero_iff,h₁.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.1]
  simp [differenceEnergy,differenceFieldEnergy,particleMoment_one,hf,
    h₁.2.2.2.2.2.2.2.2.2.1,h₁.2.2.2.2.2.2.2.2.2.2,
    h₂.2.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.2.2]

lemma differenceEnergy_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
      divergence (fun y => differenceFlux s₁ s₂ (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
        dot (s₁.E (t,x)-s₂.E (t,x)) ((s₁.f (t,x,v)-s₂.f (t,x,v)) • velocity v) := by
  have hE := (field_differentiableAt_positive h₁.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.1 ht x)
  have hB := (field_differentiableAt_positive h₁.2.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.2.1 ht x)
  have hfield : DifferentiableAt ℝ (differenceFieldEnergy s₁ s₂) (t,x) := by
    unfold differenceFieldEnergy
    convert ((hE.norm_sq (𝕜 := ℝ)).add (hB.norm_sq (𝕜 := ℝ))).mul_const (2 : ℝ)⁻¹ using 1; try rfl
  have hpart := ((squareDifference_regular_before h₁ h₂).moment_regular
    (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hflux := ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_velocity).contDiffAt
    (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hcross : DifferentiableAt ℝ (fun p => cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)) (t,x) :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp (t,x) (hE.prodMk hB)
  have hp := particle_difference_local_before h₁ h₂ ht hth x
  have hm := difference_maxwell_local_before h₁ h₂ ht hth x
  rw [deriv_time_slice (hpart.differentiableAt (by simp))] at hp
  change deriv (fun r => differenceFieldEnergy s₁ s₂ (r,x)) t + _ = _ at hm
  rw [deriv_time_slice hfield] at hm
  have hs₁ := h₁.regularParticle.slice ht.le x
  have hs₂ := h₂.regularParticle.slice ht.le x
  let g : Vec → ℝ := fun v => s₁.f (t,x,v)-s₂.f (t,x,v)
  have hgc : Continuous g := hs₁.1.continuous.sub hs₂.1.continuous
  have hgK : HasCompactSupport g := hs₁.2.sub hs₂.2
  have hdc : Continuous (fun v => fderiv ℝ (fun w => s₂.f (t,x,w)) v) :=
    hs₂.1.continuous_fderiv (by simp)
  have hi : Integrable (fun v => -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
      ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)))) :=
    (hgc.neg.mul (hdc.clm_apply (contDiff_lorentz (k := 1) _ _).continuous)).integrable_of_hasCompactSupport
      hgK.neg.mul_right
  have hjI : Integrable (fun v => g v • velocity v) :=
    (hgc.smul (contDiff_velocity (k := 1)).continuous).integrable_of_hasCompactSupport hgK.smul_right
  have hjdI : Integrable (fun v => dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) := by
    simp only [dot_eq_inner]
    exact hjI.const_inner _
  have hj : (∫ v : Vec, g v • velocity v) =
      current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x := by
    simp only [g,sub_smul,current]
    exact integral_sub
      (h₁.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
      (h₂.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
  have hdot : (∫ v : Vec, dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) =
      dot (s₁.E (t,x)-s₂.E (t,x))
        (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
    simp only [dot_eq_inner]
    rw [integral_inner hjI,hj]
  change (fderiv ℝ (differenceFieldEnergy s₁ s₂+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ))) (t,x)) (1,0) +
    divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x = _
  have hxs : DifferentiableAt ℝ (fun y => cross (s₁.E (t,y)-s₂.E (t,y))
      (s₁.B (t,y)-s₂.B (t,y))) x :=
    hcross.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hvs : DifferentiableAt ℝ (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x :=
    (hflux.differentiableAt (by simp)).comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [fderiv_add hfield (hpart.differentiableAt (by simp)),add_apply]
  have hvdiv : divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
        divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x+
        divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x := by
    exact divergence_add hxs hvs
  rw [hvdiv]
  change _ = ∫ v : Vec, -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
    ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
      dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)
  rw [integral_sub hi hjdI,hdot]
  dsimp [g] at *
  linarith

lemma differenceEnergy_zero_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) (x : Vec)
    (hz : differenceEnergy s₁ s₂ (t,x)=0) :
    s₁.E (t,x)=s₂.E (t,x) ∧ s₁.B (t,x)=s₂.B (t,x) ∧ ∀ v, s₁.f (t,x,v)=s₂.f (t,x,v) := by
  have hp : 0 ≤ (∫ v : Vec, squareDifference s₁ s₂ (t,x,v)) :=
    integral_nonneg (fun v => squareDifference_nonneg _ _ _)
  have he := differenceFieldEnergy_nonneg s₁ s₂ (t,x)
  change differenceFieldEnergy s₁ s₂ (t,x)+particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)=0 at hz
  rw [particleMoment_one] at hz
  have hp0 : (∫ v : Vec, squareDifference s₁ s₂ (t,x,v))=0 := by linarith
  have he0 : differenceFieldEnergy s₁ s₂ (t,x)=0 := by linarith
  have heq : s₁.E (t,x)=s₂.E (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.B (t,x)-s₂.B (t,x)‖,norm_nonneg (s₁.E (t,x)-s₂.E (t,x))]
  have hbq : s₁.B (t,x)=s₂.B (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.E (t,x)-s₂.E (t,x)‖,norm_nonneg (s₁.B (t,x)-s₂.B (t,x))]
  refine ⟨heq,hbq,?_⟩
  have hs := (squareDifference_regular_before h₁ h₂).slice ht x
  have hi : Integrable (fun v : Vec => squareDifference s₁ s₂ (t,x,v)) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => squareDifference_nonneg s₁ s₂ (t,x,v)) hi).mp hp0
  have hevery := Measure.eq_of_ae_eq (μ := volume) hae hs.1.continuous continuous_const
  intro v
  exact (squareDifference_zero_iff _ _ _).mp (congrFun hevery v)

lemma differenceEnergy_differential_bound_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
        divergence (fun y => differenceFlux s₁ s₂ (t,y)) x ≤
          C*differenceEnergy s₁ s₂ (t,x) := by
  obtain ⟨K₁,hK₁,hs₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hs₂⟩ := h₂.regularParticle.2 T hT
  let K : Set Vec := Prod.snd '' (K₁ ∪ K₂)
  have hK : IsCompact K := (hK₁.union hK₂).image continuous_snd
  obtain ⟨L,hL,hLb⟩ := h₂.regularParticle.velocity_derivative_bound hT
  refine ⟨(2*L+2)*(1+(volume K).toReal),by positivity,?_⟩
  intro t ht x
  rw [differenceEnergy_local_before h₁ h₂ ht.1 (ht.2.trans_le hTH) x]
  have hf₁ := h₁.regularParticle.slice ht.1.le x
  have hf₂ := h₂.regularParticle.slice ht.1.le x
  have hz : ∀ v ∉ K, s₁.f (t,x,v)-s₂.f (t,x,v)=0 := by
    intro v hv
    have hnot₁ : (x,v) ∉ tsupport (fun z => s₁.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inl (hs₁ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    have hnot₂ : (x,v) ∉ tsupport (fun z => s₂.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inr (hs₂ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot₁,image_eq_zero_of_notMem_tsupport hnot₂,sub_self]
  have hb := compact_difference_source_bound (s₁.E (t,x)-s₂.E (t,x))
    (s₁.B (t,x)-s₂.B (t,x)) (hf₁.1.continuous.sub hf₂.1.continuous)
    (hf₂.1.continuous_fderiv (by simp)) hK hz hL (hLb t ht x)
  simpa only [differenceEnergy,differenceFieldEnergy,particleMoment_one,squareDifference,Pi.sub_apply] using hb

theorem classical_unique_before {d : Datum} {s₁ s₂ : Solution} {H : ℝ}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) :
    (∀ z, s₁.f (T,z)=s₂.f (T,z)) ∧
    (∀ x, s₁.E (T,x)=s₂.E (T,x)) ∧ (∀ x, s₁.B (T,x)=s₂.B (T,x)) := by
  obtain ⟨C,hC,hbound⟩ := differenceEnergy_differential_bound_before h₁ h₂ hT hTH
  have hz := local_energy_inequality_vanishes hC hT
    (differenceEnergy_regular_before h₁ h₂) (differenceFlux_regular_before h₁ h₂)
    (differenceEnergy_continuous_slab_before h₁ h₂ hT)
    (fun _ _ _ => differenceEnergy_nonneg _ _ _)
    (fun _ ht => differenceEnergy_integrable_before h₁ h₂ ht.1)
    (differenceEnergy_integrated_continuous_before h₁ h₂ hT)
    (fun _ ht => differenceFlux_bound_before h₁ h₂ ht.1.le)
    hbound (differenceEnergy_initial_before h₁ h₂)
  have heq (x : Vec) := differenceEnergy_zero_before h₁ h₂ hT x (hz x)
  exact ⟨fun z => (heq z.1).2.2 z.2,fun x => (heq x).1,fun x => (heq x).2.1⟩

end RVM
end

end OAI
