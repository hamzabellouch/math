import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.SourceField

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM
lemma difference_source_pointwise {g L : ℝ} {D : Vec →L[ℝ] ℝ} {E B : Vec}
    (hL : 0 ≤ L) (hD : ‖D‖ ≤ L) (v : Vec) :
    -g*D (E+cross (velocity v) B)-dot E (g • velocity v) ≤
      (2*L+2)*(g^2/2+(‖E‖^2+‖B‖^2)/2) := by
  have hu := (norm_velocity_lt_one v).le
  have hK : ‖E+cross (velocity v) B‖ ≤ ‖E‖+‖B‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl
      ((norm_cross_le _ _).trans (mul_le_of_le_one_left (norm_nonneg B) hu)))
  have hd : |D (E+cross (velocity v) B)| ≤ L*(‖E‖+‖B‖) :=
    (D.le_opNorm _).trans (mul_le_mul hD hK (norm_nonneg _) hL)
  have hdot : |dot E (g • velocity v)| ≤ ‖E‖*|g| := by
    rw [dot_eq_inner]
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg g) hu) (norm_nonneg E)
  have hab : |g| *(‖E‖+‖B‖) ≤ g^2+(‖E‖^2+‖B‖^2)/2 := by
    nlinarith [sq_nonneg (|g|-‖E‖),sq_nonneg (|g|-‖B‖),sq_abs g]
  calc
    _ ≤ |g| *|D (E+cross (velocity v) B)|+|dot E (g • velocity v)| := by
      have hh := neg_le_abs (g*D (E+cross (velocity v) B))
      rw [abs_mul] at hh
      linarith [neg_le_abs (dot E (g • velocity v))]
    _ ≤ |g| *(L*(‖E‖+‖B‖))+‖E‖*|g| :=
      add_le_add (mul_le_mul_of_nonneg_left hd (abs_nonneg g)) hdot
    _ ≤ (L+1)* (|g| *(‖E‖+‖B‖)) := by
      nlinarith [mul_nonneg (abs_nonneg g) (norm_nonneg B)]
    _ ≤ (L+1)*(g^2+(‖E‖^2+‖B‖^2)/2) :=
      mul_le_mul_of_nonneg_left hab (by linarith)
    _ ≤ _ := by nlinarith [sq_nonneg ‖E‖,sq_nonneg ‖B‖]

lemma compact_difference_source_bound
    {g : Vec → ℝ} {D : Vec → (Vec →L[ℝ] ℝ)} {K : Set Vec} {L : ℝ} (E B : Vec)
    (hg : Continuous g) (hD : Continuous D) (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v=0) (hL : 0 ≤ L) (hDb : ∀ v, ‖D v‖ ≤ L) :
    (∫ v : Vec, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) ≤
      ((2*L+2)*(1+(volume K).toReal))*
        ((‖E‖^2+‖B‖^2)/2+(∫ v : Vec, (g v)^2/2)) := by
  let c : ℝ := (‖E‖^2+‖B‖^2)/2
  have hc : 0 ≤ c := div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  have hgI : Integrable (fun v : Vec => (g v)^2/2) :=
    ((hg.pow 2).div_const 2).integrable_of_hasCompactSupport (by
      apply compactSupport_of_zero_off hK
      intro v hv
      simp [hz v hv])
  have hsC : Continuous (fun v : Vec => -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) := by
    apply Continuous.sub ((hg.neg).mul (hD.clm_apply (contDiff_lorentz (k := 1) E B).continuous))
    simp_rw [dot_eq_inner]
    exact continuous_const.inner (hg.smul (contDiff_velocity (k := 1)).continuous)
  have hs0 : ∀ v ∉ K, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v) = 0 := by
    intro v hv
    simp [hz v hv,dot]
  have hsI : Integrable (fun v : Vec => -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) := hsC.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK hs0)
  have hcI : IntegrableOn (fun _ : Vec => c) K volume :=
    integrableOn_const hK.measure_lt_top.ne
  have hm : (∫ v : Vec, (g v)^2/2) ≥ 0 := integral_nonneg (fun v => by positivity)
  calc
    _ = ∫ v in K, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hs0).symm
    _ ≤ ∫ v in K, (2*L+2)*((g v)^2/2+c) := by
      apply integral_mono hsI.integrableOn ((hgI.integrableOn.add hcI).const_mul _)
      intro v
      exact difference_source_pointwise hL (hDb v) v
    _ = (2*L+2)*((∫ v : Vec, (g v)^2/2)+(volume K).toReal*c) := by
      rw [integral_const_mul,integral_add hgI.integrableOn hcI,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by simp [hz v hv]),
        integral_const]
      simp [measureReal_def]
    _ ≤ _ := by
      have hv := ENNReal.toReal_nonneg (a := volume K)
      dsimp [c] at *
      nlinarith [mul_nonneg hv hm,mul_nonneg (by linarith : 0 ≤ 2*L+2)
        (add_nonneg (mul_nonneg hv hm) hc)]

lemma squareDifference_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
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

lemma particleMoment_one (f : Particle) (p : ℝ × Vec) :
    particleMoment f (fun _ => (1:ℝ)) p = ∫ v : Vec, f (p.1,p.2,v) := by
  simp [particleMoment]

lemma RegularParticle.moment_component {f : Particle} (hf : RegularParticle f)
    {w : Vec → Vec} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (x : Vec) (i : Fin 3) :
    particleMoment f w (t,x) i = ∫ v : Vec, w v i * f (t,x,v) := by
  have hi := hf.moment_integrable hw ht x
  have he := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa [particleMoment,mul_comm] using he.symm

lemma particle_difference_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
    deriv (fun r => particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (r,x)) t +
      divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hf := squareDifference_regular h₁ h₂
  obtain ⟨U,K,hU,hK,hp,hF,hz⟩ := hf.local_data ht x
  have he := particle_number_balance_param (s₁.E (t,x)) (s₁.B (t,x)) hU hK hp hF hz
  have he' : (∫ v : Vec, fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x)))) = _ :=
    integral_congr_ae (Filter.Eventually.of_forall (particle_difference_direction h₁ h₂ ht x))
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

lemma curl_sub {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    curl (F-G) x = curl F x - curl G x := by
  have h (i : Fin 3) : fderiv ℝ (fun y => F y i-G y i) x =
      fderiv ℝ (fun y => F y i) x - fderiv ℝ (fun y => G y i) x := by
    exact fderiv_sub
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF)
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG)
  ext i
  fin_cases i <;> simp [curl,spatialPartial,h] <;> ring

lemma difference_maxwell_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
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
  have he₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le).2.1 x
  have hb₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le).2.2.1 x
  have he₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le).2.1 x
  have hb₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le).2.2.1 x
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

def differenceFieldEnergy (s₁ s₂ : Solution) (p : ℝ × Vec) : ℝ :=
  (‖s₁.E p-s₂.E p‖^2+‖s₁.B p-s₂.B p‖^2)/2

def differenceEnergy (s₁ s₂ : Solution) (p : ℝ × Vec) : ℝ :=
  differenceFieldEnergy s₁ s₂ p+particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) p

def differenceFlux (s₁ s₂ : Solution) (p : ℝ × Vec) : Vec :=
  cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)+particleMoment (squareDifference s₁ s₂) velocity p

lemma differenceFieldEnergy_nonneg (s₁ s₂ : Solution) (p : ℝ × Vec) :
    0 ≤ differenceFieldEnergy s₁ s₂ p := by
  exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)

lemma differenceEnergy_nonneg (s₁ s₂ : Solution) (p : ℝ × Vec) :
    0 ≤ differenceEnergy s₁ s₂ p := by
  apply add_nonneg (differenceFieldEnergy_nonneg _ _ _)
  rw [particleMoment_one]
  exact integral_nonneg (fun v => squareDifference_nonneg _ _ _)

lemma differenceEnergy_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
    ContDiffOn ℝ 1 (differenceEnergy s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((he.norm_sq ℝ).add (hb.norm_sq ℝ)).div_const 2 |>.add
    ((squareDifference_regular h₁ h₂).moment_regular contDiff_const)

lemma differenceFlux_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
    ContDiffOn ℝ 1 (differenceFlux s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (he.prodMk hb)
    (fun _ _ => mem_univ _)).add
      ((squareDifference_regular h₁ h₂).moment_regular contDiff_velocity)

lemma differenceEnergy_continuous_slab {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (differenceEnergy s₁ s₂) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.continuousOn.sub h₂.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  have hb := (h₁.2.2.1.continuousOn.sub h₂.2.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  exact ((he.norm.pow 2).add (hb.norm.pow 2)).div_const 2 |>.add
    ((squareDifference_regular h₁ h₂).moment_continuous_slab continuous_const hT)

lemma differenceEnergy_integrable {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => differenceEnergy s₁ s₂ (t,x)) := by
  exact (((h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht).add
    ((h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht)).div_const 2 |>.add
      ((squareDifference_regular h₁ h₂).spatial_moment_integrable continuous_const ht)

lemma differenceEnergy_integrated_continuous {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, differenceEnergy s₁ s₂ (t,x)) (Icc 0 T) := by
  have he := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hb := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hp := (squareDifference_regular h₁ h₂).integrated_moment_continuous
    (w := fun _ => (1:ℝ)) continuous_const hT
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) = _
  have hiE := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht.1
  have hiB := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht.1
  have hiP := (squareDifference_regular h₁ h₂).spatial_moment_integrable
    (w := fun _ => (1:ℝ)) continuous_const ht.1
  calc
    _ = (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2)+
      (∫ x : Vec, particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) :=
        integral_add ((hiE.add hiB).div_const 2) hiP
    _ = _ := by rw [integral_div,integral_add hiE hiB]; rfl

lemma differenceFlux_bound {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖differenceFlux s₁ s₂ (t,x)‖ ≤ differenceEnergy s₁ s₂ (t,x) := by
  apply (norm_add_le _ _).trans
  apply add_le_add ?_ ((squareDifference_regular h₁ h₂).velocity_flux_bound ht x
    (fun v => squareDifference_nonneg _ _ _))
  apply (norm_cross_le _ _).trans
  dsimp [differenceFieldEnergy]
  nlinarith [sq_nonneg (‖s₁.E (t,x)-s₂.E (t,x)‖-‖s₁.B (t,x)-s₂.B (t,x)‖)]

lemma differenceEnergy_initial {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) (x : Vec) :
    differenceEnergy s₁ s₂ (0,x) = 0 := by
  have hf (v : Vec) : squareDifference s₁ s₂ (0,x,v)=0 := by
    rw [squareDifference_zero_iff,h₁.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.1]
  simp [differenceEnergy,differenceFieldEnergy,particleMoment_one,hf,
    h₁.2.2.2.2.2.2.2.2.2.1,h₁.2.2.2.2.2.2.2.2.2.2,
    h₂.2.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.2.2]

lemma differenceEnergy_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
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
  have hpart := ((squareDifference_regular h₁ h₂).moment_regular
    (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hflux := ((squareDifference_regular h₁ h₂).moment_regular contDiff_velocity).contDiffAt
    (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hcross : DifferentiableAt ℝ (fun p => cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)) (t,x) :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp (t,x) (hE.prodMk hB)
  have hp := particle_difference_local h₁ h₂ ht x
  have hm := difference_maxwell_local h₁ h₂ ht x
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

lemma differenceEnergy_zero {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) (x : Vec)
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
  have hs := (squareDifference_regular h₁ h₂).slice ht x
  have hi : Integrable (fun v : Vec => squareDifference s₁ s₂ (t,x,v)) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => squareDifference_nonneg s₁ s₂ (t,x,v)) hi).mp hp0
  have hevery := Measure.eq_of_ae_eq (μ := volume) hae hs.1.continuous continuous_const
  intro v
  exact (squareDifference_zero_iff _ _ _).mp (congrFun hevery v)

lemma differenceEnergy_differential_bound {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
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
  rw [differenceEnergy_local h₁ h₂ ht.1 x]
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

theorem classical_unique {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) : SameNonnegativeTime s₁ s₂ := by
  intro T hT
  obtain ⟨C,hC,hbound⟩ := differenceEnergy_differential_bound h₁ h₂ hT
  have hz := local_energy_inequality_vanishes hC hT
    (differenceEnergy_regular h₁ h₂) (differenceFlux_regular h₁ h₂)
    (differenceEnergy_continuous_slab h₁ h₂ hT)
    (fun _ _ _ => differenceEnergy_nonneg _ _ _)
    (fun _ ht => differenceEnergy_integrable h₁ h₂ ht.1)
    (differenceEnergy_integrated_continuous h₁ h₂ hT)
    (fun _ ht => differenceFlux_bound h₁ h₂ ht.1.le)
    hbound (differenceEnergy_initial h₁ h₂)
  have heq (x : Vec) := differenceEnergy_zero h₁ h₂ hT x (hz x)
  exact ⟨fun z => (heq z.1).2.2 z.2,fun x => (heq x).1,fun x => (heq x).2.1⟩

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM
lemma vacuum_energy_conservation {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => maxwellEnergy E B (t,x)) ∧
    (∫ x : Vec, maxwellEnergy E B (t,x))=∫ x : Vec, maxwellEnergy E B (0,x) := by
  apply causal_energy_conserved (contDiff_maxwellEnergy hE hB) (contDiff_maxwellFlux hE hB) ht
    (fun _ _ _ => maxwellEnergy_nonneg _ _ _)
    (fun _ _ _ => maxwellFlux_le _ _ _) (fun r hr x => ?_)
    (((memLp_two_iff_integrable_sq_norm hE0.aestronglyMeasurable).mp hE0).add
      ((memLp_two_iff_integrable_sq_norm hB0.aestronglyMeasurable).mp hB0) |>.div_const 2)
  have h1 := (hfirst r hr.1.le x).1
  have h2 := (hfirst r hr.1.le x).2
  have hh := maxwell_energy_balance (hE.differentiable (by simp) (r,x))
    (hB.differentiable (by simp) (r,x)) (j:=0) (by
      rw [deriv_slice_eq_dirD (hE.differentiable (by simp)),
        ← spaceCurl_slice (hB.differentiable (by simp)),h1,sub_self,neg_zero]) (by
      rw [deriv_slice_eq_dirD (hB.differentiable (by simp)),
        ← spaceCurl_slice (hE.differentiable (by simp)),h2,neg_add_cancel])
  simpa only [maxwellEnergy,maxwellFlux,dot,PiLp.zero_apply,mul_zero,Finset.sum_const_zero,neg_zero] using hh

lemma vacuum_memLp {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (fun x => E (t,x)) 2 volume ∧ MemLp (fun x => B (t,x)) 2 volume := by
  have hI := ((vacuum_energy_conservation hE hB hfirst hE0 hB0 ht).1).const_mul 2
  have hEc : Continuous (fun x : Vec => E (t,x)) :=
    hE.continuous.comp (continuous_const.prodMk continuous_id)
  have hBc : Continuous (fun x : Vec => B (t,x)) :=
    hB.continuous.comp (continuous_const.prodMk continuous_id)
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hEc.aestronglyMeasurable).mpr
    apply hI.mono_nonneg (hEc.norm.pow 2).aestronglyMeasurable (ae_of_all _ (fun x => sq_nonneg _))
    filter_upwards with x
    simp only [Pi.pow_apply]
    dsimp only [maxwellEnergy]
    nlinarith [sq_nonneg ‖B (t,x)‖]
  · apply (memLp_two_iff_integrable_sq_norm hBc.aestronglyMeasurable).mpr
    apply hI.mono_nonneg (hBc.norm.pow 2).aestronglyMeasurable (ae_of_all _ (fun x => sq_nonneg _))
    filter_upwards with x
    simp only [Pi.pow_apply]
    dsimp only [maxwellEnergy]
    nlinarith [sq_nonneg ‖E (t,x)‖]

lemma norm_sub_sq_le_twice (x y : Vec) :
    ‖x-y‖^2  ≤  2*‖x‖^2+2*‖y‖^2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg (x-y),norm_nonneg x,norm_nonneg y,sq_nonneg (‖x‖-‖y‖)]

lemma pair_sq_difference_tendsto {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0))
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => ∫ x : Vec, ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2)
      (𝓝[Ici 0] s) (𝓝 0) := by
  let e : ℝ → Vec → ℝ := fun t x => ‖E (t,x)‖^2+‖B (t,x)‖^2
  let D : ℝ → Vec → ℝ := fun t x => ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2
  let g : ℝ → Vec → ℝ := fun t x => min (4*e s x) (2*e t x+2*e s x-D t x)
  have heI (t : ℝ) (ht : 0 ≤ t) : Integrable (e t) :=
    ((memLp_two_iff_integrable_sq_norm (hLp t ht).1.aestronglyMeasurable).mp (hLp t ht).1).add
      ((memLp_two_iff_integrable_sq_norm (hLp t ht).2.aestronglyMeasurable).mp (hLp t ht).2)
  have hDI (t : ℝ) (ht : 0 ≤ t) : Integrable (D t) := by
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt).add
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt)
  have hD0 (t : ℝ) (x : Vec) : 0 ≤ D t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he0 (t : ℝ) (x : Vec) : 0 ≤ e t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hDle (t : ℝ) (x : Vec) : D t x ≤ 2*e t x+2*e s x := by
    have h1 := norm_sub_sq_le_twice (E (t,x)) (E (s,x))
    have h2 := norm_sub_sq_le_twice (B (t,x)) (B (s,x))
    dsimp only [D,e]
    linarith
  have hg0 (t : ℝ) (x : Vec) : 0 ≤ g t x :=
    le_min (mul_nonneg (by norm_num) (he0 s x)) (sub_nonneg.mpr (hDle t x))
  have hgI (t : ℝ) (ht : 0 ≤ t) : Integrable (g t) :=
    ((heI s hs).const_mul 4).inf (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
  have hgc (x : Vec) : Continuous (fun t => g t x) := by
    apply continuous_const.min
    exact ((((hE.comp (continuous_id.prodMk continuous_const)).norm.pow 2).add
      ((hB.comp (continuous_id.prodMk continuous_const)).norm.pow 2)).const_mul 2 |>.add continuous_const |>.sub
      ((((hE.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2).add
        (((hB.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2)))
  have hgs (x : Vec) : g s x=4*e s x := by
    dsimp only [g,D]
    simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),add_zero,sub_zero]
    rw [show 2*e s x+2*e s x=4*e s x by ring,min_self]
  have hglim : Tendsto (fun t => ∫ x : Vec, g t x) (𝓝[Ici 0] s) (𝓝 (4*∫ x : Vec, e s x)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_filter_of_dominated_convergence (fun x => 4*e s x)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hgI t ht).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (hg0 t x)]
        exact min_le_left _ _))
    · exact (heI s hs).const_mul 4
    · exact ae_of_all _ (fun x => by
        simpa only [hgs] using
          ((hgc x).continuousAt (x:=s)).continuousWithinAt (s:=Ici 0) |>.tendsto)
  have hlim : Tendsto (fun t => 2*(∫ x : Vec, e t x)+2*(∫ x : Vec, e s x)-∫ x : Vec, g t x)
      (𝓝[Ici 0] s) (𝓝 0) := by
    have hh := (((henergy s hs).tendsto.const_mul 2).add_const (2*∫ x : Vec, e s x)).sub hglim
    convert hh using 1
    dsimp only [e]
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun t => integral_nonneg (hD0 t))) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hm : (∫ x : Vec, g t x) ≤ ∫ x : Vec, 2*e t x+2*e s x-D t x :=
    integral_mono (hgI t ht) (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
      (fun x => min_le_right _ _)
  have hsum : Integrable (fun x => 2*e t x+2*e s x) :=
    ((heI t ht).const_mul 2).add ((heI s hs).const_mul 2)
  rw [integral_sub hsum (hDI t ht),
    integral_add ((heI t ht).const_mul 2) ((heI s hs).const_mul 2),integral_const_mul,integral_const_mul] at hm
  linarith

lemma L2_norm_sub_sq_eq_integral {u v : Lp Vec 2 (volume : Measure Vec)}
    {f g : Vec → Vec} (hu : (u : Vec → Vec) =ᵐ[volume] f)
    (hv : (v : Vec → Vec) =ᵐ[volume] g) :
    ‖u-v‖^2=∫ x : Vec, ‖f x-g x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v,hu,hv] with x hsub hf hg
  rw [hsub]
  simp only [Pi.sub_apply,hf,hg,real_inner_self_eq_norm_sq]

lemma timeContinuousL2_of_continuous_energy {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0)) :
    TimeContinuousL2 E ∧ TimeContinuousL2 B := by
  classical
  let E₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).1.toLp (fun x => E (t,x)) else 0
  let B₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).2.toLp (fun x => B (t,x)) else 0
  have hEe (t : ℝ) (ht : 0 ≤ t) : (E₂ t : Vec → Vec) =ᵐ[volume] (fun x => E (t,x)) := by
    dsimp only [E₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hBe (t : ℝ) (ht : 0 ≤ t) : (B₂ t : Vec → Vec) =ᵐ[volume] (fun x => B (t,x)) := by
    dsimp only [B₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hlim (s : ℝ) (hs : 0 ≤ s) :
      Tendsto (fun t => ‖E₂ t-E₂ s‖^2+‖B₂ t-B₂ s‖^2) (𝓝[Ici 0] s) (𝓝 0) := by
    apply (pair_sq_difference_tendsto hE hB hLp henergy hs).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [L2_norm_sub_sq_eq_integral (hEe t ht) (hEe s hs),
      L2_norm_sub_sq_eq_integral (hBe t ht) (hBe s hs)]
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact (integral_add
      ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt)
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt))
  have hEc : ContinuousOn E₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖E₂ t-E₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_right (sq_nonneg ‖B₂ t-B₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  have hBc : ContinuousOn B₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖B₂ t-B₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_left (sq_nonneg ‖E₂ t-E₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  exact ⟨⟨E₂,hEc,hEe⟩,⟨B₂,hBc,hBe⟩⟩

theorem vacuum_timeContinuousL2 {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hfirst : ∀ t, 0 ≤ t → ∀ x, dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hE0 : MemLp (fun x => E (0,x)) 2 volume) (hB0 : MemLp (fun x => B (0,x)) 2 volume) :
    TimeContinuousL2 E ∧ TimeContinuousL2 B := by
  apply timeContinuousL2_of_continuous_energy hE.continuous hB.continuous
    (fun t ht => vacuum_memLp hE hB hfirst hE0 hB0 ht)
  have heq (t : ℝ) (ht : t∈Ici 0) :
      (∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2)=2*∫ x : Vec, maxwellEnergy E B (0,x) := by
    calc
      _ = 2*∫ x : Vec, maxwellEnergy E B (t,x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp only [maxwellEnergy]; ring)
      _ = _ := congrArg (fun y : ℝ => 2*y) (vacuum_energy_conservation hE hB hfirst hE0 hB0 ht).2
  exact continuousOn_const.congr (fun t ht => heq t ht)

def freeMaxwellElectric (E₀ B₀ : Vec → Vec) : Field :=
  maxwellElectric E₀ B₀ (fun p => divergence E₀ p.2) 0

def freeMaxwellMagnetic (E₀ B₀ : Vec → Vec) : Field := maxwellMagnetic E₀ B₀ 0

lemma initialCharge_conserved {E₀ : Vec → Vec} (hE : ContDiff ℝ ∞ E₀)
    (p : ℝ × Vec) :
    dirD (fun z : ℝ × Vec => divergence E₀ z.2) (1,0) p+spaceDiv (0:Field) p=0 := by
  rcases p with ⟨t,x⟩
  have hρ : ContDiff ℝ ∞ (fun z : ℝ × Vec => divergence E₀ z.2) :=
    (contDiff_divergence hE).comp contDiff_snd
  rw [← deriv_slice_eq_dirD (hρ.differentiable (by simp))]
  simp [spaceDiv,dirD]

lemma freeMaxwell_equations {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hDB : ∀ x, divergence B₀ x=0) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD (freeMaxwellElectric E₀ B₀) (1,0) (t,x)=spaceCurl (freeMaxwellMagnetic E₀ B₀) (t,x) ∧
    dirD (freeMaxwellMagnetic E₀ B₀) (1,0) (t,x)= -spaceCurl (freeMaxwellElectric E₀ B₀) (t,x) ∧
    spaceDiv (freeMaxwellElectric E₀ B₀) (t,x)=divergence E₀ x ∧
    spaceDiv (freeMaxwellMagnetic E₀ B₀) (t,x)=0 := by
  have hh := constructed_maxwell_equations (j:=0) hE hB
    ((contDiff_divergence hE).comp contDiff_snd) (contDiff_const : ContDiff ℝ ∞ (0:Field))
    (fun t _ x => initialCharge_conserved hE (t,x)) (fun _ => rfl) hDB ht x
  change dirD (freeMaxwellElectric E₀ B₀) (1,0) (t,x)=spaceCurl (freeMaxwellMagnetic E₀ B₀) (t,x)-(0:Vec) ∧
    dirD (freeMaxwellMagnetic E₀ B₀) (1,0) (t,x)= -spaceCurl (freeMaxwellElectric E₀ B₀) (t,x) ∧
    spaceDiv (freeMaxwellElectric E₀ B₀) (t,x)=divergence E₀ x ∧
    spaceDiv (freeMaxwellMagnetic E₀ B₀) (t,x)=0 at hh
  simpa only [sub_zero] using hh

theorem freeMaxwell_evolution {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hE0 : MemLp E₀ 2 volume) (hB0 : MemLp B₀ 2 volume)
    (hDB : ∀ x, divergence B₀ x=0) :
    let E := freeMaxwellElectric E₀ B₀
    let B := freeMaxwellMagnetic E₀ B₀
    ContDiff ℝ ∞ E ∧ ContDiff ℝ ∞ B ∧
    (∀ x, E (0,x)=E₀ x ∧ B (0,x)=B₀ x) ∧
    TimeContinuousL2 E ∧ TimeContinuousL2 B ∧
    (∀ t, 0 ≤ t → ∀ x,
      dirD E (1,0) (t,x)=spaceCurl B (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x) ∧
      spaceDiv E (t,x)=divergence E₀ x ∧ spaceDiv B (t,x)=0) := by
  have hEc : ContDiff ℝ ∞ (freeMaxwellElectric E₀ B₀) :=
    contDiff_maxwellElectric hE hB ((contDiff_divergence hE).comp contDiff_snd) contDiff_const
  have hBc : ContDiff ℝ ∞ (freeMaxwellMagnetic E₀ B₀) :=
    contDiff_maxwellMagnetic hE hB contDiff_const
  have hEi (x : Vec) : freeMaxwellElectric E₀ B₀ (0,x)=E₀ x := maxwellElectric_initial hE x
  have hBi (x : Vec) : freeMaxwellMagnetic E₀ B₀ (0,x)=B₀ x := maxwellMagnetic_initial hB x
  have hfirst (t : ℝ) (ht : 0 ≤ t) (x : Vec) := freeMaxwell_equations hE hB hDB ht x
  have hEI : MemLp (fun x => freeMaxwellElectric E₀ B₀ (0,x)) 2 volume := by
    simpa only [hEi] using hE0
  have hBI : MemLp (fun x => freeMaxwellMagnetic E₀ B₀ (0,x)) 2 volume := by
    simpa only [hBi] using hB0
  obtain ⟨hEl2,hBl2⟩ := vacuum_timeContinuousL2 hEc hBc
    (fun t ht x => ⟨(hfirst t ht x).1,(hfirst t ht x).2.1⟩) hEI hBI
  exact ⟨hEc,hBc,(fun x => ⟨hEi x,hBi x⟩),hEl2,hBl2,hfirst⟩

lemma derivWithin_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) {t : ℝ} (ht : 0 ≤ t) (x : H) :
    derivWithin (fun r => F (r,x)) (Ici 0) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 t ht)

theorem global_classical_solution_of_zero_particles (d : Datum) (hd : Admissible d)
    (hf : d.f₀ = 0) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  obtain ⟨_,_,_,hE,hB,hEL,hBL,hDE,hDB⟩ := hd
  obtain ⟨hEs,hBs,hinit,hEL2,hBL2,heq⟩ :=
    freeMaxwell_evolution hE.1 hB.1 hEL hBL hDB
  let s : Solution := ⟨0,freeMaxwellElectric d.E₀ d.B₀,freeMaxwellMagnetic d.E₀ d.B₀⟩
  have hclass : Classical d s := by
    refine ⟨contDiffOn_const,hEs.of_le (by simp) |>.contDiffOn,
      hBs.of_le (by simp) |>.contDiffOn,?_,hEL2,hBL2,?_,?_,?_,?_,?_⟩
    · intro t ht z; exact le_rfl
    · intro T hT
      exact ⟨∅,isCompact_empty,fun t ht => by simp [s,tsupport]⟩
    · intro t ht
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro x v; simp [s,spatialPartial]
      · intro x
        change derivWithin (fun r => s.E (r,x)) (Ici 0) t - curl (fun y => s.B (t,y)) x = _
        rw [derivWithin_slice_eq_dirD (hEs.differentiable (by simp)) ht,
          (heq t ht x).1,spaceCurl_slice (hBs.differentiable (by simp))]
        simp [s,current]
      · intro x
        rw [derivWithin_slice_eq_dirD (hBs.differentiable (by simp)) ht,
          (heq t ht x).2.1,spaceCurl_slice (hEs.differentiable (by simp))]
        simp [s]
      · intro x
        rw [← spaceDiv_slice (hEs.differentiable (by simp)),(heq t ht x).2.2.1,hDE x]
        simp [s,rho,hf]
      · intro x
        rw [← spaceDiv_slice (hBs.differentiable (by simp))]
        exact (heq t ht x).2.2.2
    · intro z; simp [s,hf]
    · intro x; exact (hinit x).1
    · intro x; exact (hinit x).2
  refine ⟨s,hclass,?_,fun s' hs' => classical_unique hclass hs'⟩
  intro T hT
  exact ⟨contDiffOn_const,hEs.contDiffOn,hBs.contDiffOn⟩

end RVM

end

end OAI
