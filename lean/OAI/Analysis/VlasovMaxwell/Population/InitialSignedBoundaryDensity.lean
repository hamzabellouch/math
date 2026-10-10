import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.BranchIntegral

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PhaseFlowOn.retarded_radius_separated {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX zY : Phase)
    (hne : ∀ t∈Icc 0 T,(F.flow zX t).1≠(F.flow zY t).1) :
    ∃ δ : ℝ,0<δ ∧ ∀ σ∈branchDomain F.flow zX zY T,
      δ≤branchTime F.flow zX zY T σ-σ := by
  have hc : ContinuousOn (fun t=>‖(F.flow zX t).1-(F.flow zY t).1‖) (Icc 0 T) :=
    ((F.continuousOn_time zX).fst.sub (F.continuousOn_time zY).fst).norm
  obtain ⟨t₀,ht₀,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) hc
  have hpos : 0<‖(F.flow zX t₀).1-(F.flow zY t₀).1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hne t₀ ht₀))
  obtain ⟨c,hc1,hLip⟩ := F.timelike hT zY
  refine ⟨‖(F.flow zX t₀).1-(F.flow zY t₀).1‖/2,by positivity,?_⟩
  intro σ hσ
  let τ := branchTime F.flow zX zY T σ
  have ht := (F.branch_spec zX zY hσ).1
  have ht0 : τ∈Icc 0 T := ⟨hσ.1.1.le.trans ht.1,ht.2⟩
  have hr : 0≤τ-σ := sub_nonneg.mpr ht.1
  have hdist := hLip.dist_le_mul τ ht0 σ (Ioo_subset_Icc_self hσ.1)
  rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg hr] at hdist
  have hbound : ‖(F.flow zY τ).1-(F.flow zY σ).1‖≤τ-σ :=
    hdist.trans (mul_le_of_le_one_left hr hc1.le)
  have hcone := (F.branch_spec zX zY hσ).2
  have htriangle : ‖(F.flow zX τ).1-(F.flow zY τ).1‖ ≤
      ‖(F.flow zX τ).1-(F.flow zY σ).1‖+‖(F.flow zY σ).1-(F.flow zY τ).1‖ := by
    calc
      _ = ‖((F.flow zX τ).1-(F.flow zY σ).1)+((F.flow zY σ).1-(F.flow zY τ).1)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (F.flow zY σ).1 (F.flow zY τ).1] at htriangle
  have hm := hmin ht0
  change ‖(F.flow zX t₀).1-(F.flow zY t₀).1‖≤‖(F.flow zX τ).1-(F.flow zY τ).1‖ at hm
  change τ-σ=‖(F.flow zX τ).1-(F.flow zY σ).1‖ at hcone
  change _≤τ-σ
  linarith

lemma PhaseFlowOn.ae_retarded_radius_separated {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ∀ᵐ zY ∂(volume : Measure Phase), ∃ δ : ℝ,0<δ ∧
      ∀ σ∈branchDomain F.flow zX zY T,δ≤branchTime F.flow zX zY T σ-σ := by
  have hh : ∀ᵐ zY ∂(volume : Measure Phase),
      zY∉{y : Phase | ∃ t∈Icc 0 T,(F.flow y t).1=(F.flow zX t).1} :=
    ae_iff.mpr (by simpa only [Set.mem_ofPred_eq,not_not] using F.closed_collision_null hT zX)
  filter_upwards [hh] with zY hzY
  apply F.retarded_radius_separated hT zX zY
  intro t ht he
  exact hzY ⟨t,ht,he.symm⟩

lemma signedPrimitive_scaled (a u n : Vec) (hD : 1-dot n a≠0) :
    (1-dot n a) • signedPrimitive a u n =
      (1-dot n a) • u-(1-dot a u) • n := by
  rw [signedPrimitive,smul_sub,smul_smul,mul_div_cancel₀ _ hD]

lemma signedPrimitive_scaled_norm (w v n : Vec) (hn : ‖n‖=1) :
    ‖(1-dot n (velocity w)) • signedPrimitive (velocity w) (velocity v) n‖≤4 := by
  rw [signedPrimitive_scaled _ _ _ (cone_denom_pos w n hn).ne']
  have he : |1-dot (velocity w) (velocity v)|≤2 :=
    (abs_sub _ _).trans (by
      have hh := abs_dot_le (velocity w) (velocity v)
      have hu := norm_velocity_lt_one w
      have hv := norm_velocity_lt_one v
      have hprod : ‖velocity w‖*‖velocity v‖≤1 :=
        (mul_le_of_le_one_left (norm_nonneg _) hu.le).trans hv.le
      norm_num only [abs_one]
      linarith)
  calc
    _ ≤ ‖(1-dot n (velocity w)) • velocity v‖+‖(1-dot (velocity w) (velocity v)) • n‖ := norm_sub_le _ _
    _ = (1-dot n (velocity w))*‖velocity v‖+|1-dot (velocity w) (velocity v)| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hn,mul_one,
        abs_of_pos (cone_denom_pos w n hn)]
    _ ≤ 2*1+2 := by
      gcongr
      · exact cone_denom_le_two w n hn
      · exact (norm_velocity_lt_one v).le
    _ = 4 := by norm_num

def initialSignedBoundaryDensity (f : Phase→ℝ) (x w : Vec) (t ψ χ : ℝ)
    (P : Vec→L[ℝ]Vec) (n v : Vec) : Vec :=
  (t^2*(1-dot n (velocity w))*f (x-t • n,v)*ψ*χ) •
    P (retardedPrimitive t (velocity w) (velocity v) n)

lemma initialSignedBoundaryDensity_eq (f : Phase→ℝ) (x w : Vec) (t ψ χ : ℝ)
    (P : Vec→L[ℝ]Vec) (n v : Vec) :
    initialSignedBoundaryDensity f x w t ψ χ P n v =
      (t*ψ*χ*f (x-t • n,v)/(1-dot n (velocity v))) •
        P ((1-dot n (velocity w)) • signedPrimitive (velocity w) (velocity v) n) := by
  simp only [initialSignedBoundaryDensity,retardedPrimitive,map_smul,smul_smul]
  congr 1
  by_cases ht : t=0
  · simp [ht]
  · by_cases hd : 1-dot n (velocity v)=0
    · simp [hd]
    · field_simp

lemma initialSignedBoundaryDensity_norm (f : Phase→ℝ) (hf : ∀ z,0≤f z)
    (x w : Vec) {t χ M : ℝ} (ht : 0≤t) (hχ : χ∈Icc (0:ℝ) 1)
    (ψ : ℝ) (P : Vec→L[ℝ]Vec) (hP : ‖P‖≤M) (n v : Vec) (hn : ‖n‖=1) :
    ‖initialSignedBoundaryDensity f x w t ψ χ P n v‖≤
      (4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v))) := by
  have hM : 0≤M := (norm_nonneg P).trans hP
  have hd := cone_denom_pos v n hn
  have hfv := hf (x-t • n,v)
  have hχ0 := hχ.1
  rw [initialSignedBoundaryDensity_eq f x w t ψ χ P n v,
    norm_smul,Real.norm_eq_abs,abs_div,abs_mul,abs_mul,abs_mul,
    abs_of_nonneg ht,abs_of_nonneg hχ.1,abs_of_nonneg (hf _),abs_of_pos hd]
  calc
    _ ≤ (t*|ψ| *χ*f (x-t • n,v)/(1-dot n (velocity v)))*(M*4) := by
      apply mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm P _).trans
          (mul_le_mul hP (signedPrimitive_scaled_norm w v n hn) (norm_nonneg _) hM))
      positivity
    _ ≤ (t*|ψ| *1*f (x-t • n,v)/(1-dot n (velocity v)))*(M*4) := by
      gcongr
      exact hχ.2
    _ = _ := by ring

lemma datum_reciprocal_cone_bound {f : Phase→ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    :
    ∃ C : ℝ,0≤C ∧ ∀ y n : Vec,‖n‖=1 →
      Integrable (fun v : Vec=>f (y,v)/(1-dot n (velocity v))) ∧
      (∫ v : Vec,f (y,v)/(1-dot n (velocity v)))≤C := by
  have hu : Continuous (fun p : Vec×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec×Vec=>1-dot p.1 (velocity p.2)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_fst.prodMk hu))
  have hi : ContinuousOn (fun p : Vec×Vec=>(1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
        intro p hp
        exact (cone_denom_pos p.2 p.1 (mem_sphere_zero_iff_norm.mp hp.1)).ne')
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc hi
  refine ⟨C,hC,?_⟩
  intro y n hn
  have hdv : Continuous (fun v : Vec=>1-dot n (velocity v)) :=
    hd.comp (continuous_const.prodMk continuous_id)
  have hh : Continuous (fun v : Vec=>f (y,v)/(1-dot n (velocity v))) :=
    (hf.comp (continuous_const.prodMk continuous_id)).div hdv (fun v=>(cone_denom_pos v n hn).ne')
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  refine ⟨hh.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK ?_),?_⟩
  · intro v hv
    rw [hz y v hv,zero_div]
  · have hh := hbound y n hn
    simp only [smul_eq_mul,← div_eq_mul_inv,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh

lemma initialSignedBoundary_velocity_bound {f : Phase→ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (x w : Vec) (t ψ M : ℝ) (χ : Vec→ℝ) (P : Vec→L[ℝ]Vec)
      (n : Vec), 0≤t → (∀ v,χ v∈Icc (0:ℝ) 1) → ‖P‖≤M → ‖n‖=1 →
      ‖∫ v : Vec,initialSignedBoundaryDensity f x w t ψ (χ v) P n v‖≤
        C*t*|ψ| *M := by
  obtain ⟨C,hC,hbound⟩ := datum_reciprocal_cone_bound hf hc
  refine ⟨4*C,by positivity,?_⟩
  intro x w t ψ M χ P n ht hχ hP hn
  have hM : 0≤M := (norm_nonneg P).trans hP
  obtain ⟨hgi,hgb⟩ := hbound (x-t • n) n hn
  have hb := norm_integral_le_of_norm_le (hgi.const_mul (4*t*|ψ| *M))
    (ae_of_all _ (fun v=>initialSignedBoundaryDensity_norm f hpos x w ht (hχ v) ψ P hP n v hn))
  rw [integral_const_mul] at hb
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hgb (show 0≤4*t*|ψ| *M by positivity)])

lemma initialSignedBoundary_bound {f : Phase→ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (T M : ℝ) (J : Set ℝ) (X V : ℝ→Vec)
      (ψ : ℝ→ℝ) (χ : ℝ→Sphere→Vec→ℝ) (P : ℝ→Vec→L[ℝ]Vec),
      0≤T → 0≤M → MeasurableSet J → J⊆Icc 0 T → IntegrableOn ψ J →
      (∀ t∈J,∀ n v,χ t n v∈Icc (0:ℝ) 1) → (∀ t∈J,‖P t‖≤M) →
      ‖∫ t in J,∫ n : Sphere,∫ v : Vec,
        initialSignedBoundaryDensity f (X t) (V t) t (ψ t) (χ t n v) (P t) n.1 v
          ∂volume ∂sphereMeasure‖ ≤ C*T*M*(∫ t in J,|ψ t|) := by
  obtain ⟨C,hC,hb⟩ := initialSignedBoundary_velocity_bound hf hc hpos
  refine ⟨C*(4*Real.pi),by positivity,?_⟩
  intro T M J X V ψ χ P hT hM hJ hJT hψ hχ hP
  have hpoint : ∀ t∈J,
      ‖∫ n : Sphere,∫ v : Vec,
        initialSignedBoundaryDensity f (X t) (V t) t (ψ t) (χ t n v) (P t) n.1 v
          ∂volume ∂sphereMeasure‖ ≤ (C*(4*Real.pi)*T*M)*|ψ t| := by
    intro t ht
    have hh := norm_sphere_integral_le (fun n : Sphere =>
      hb (X t) (V t) t (ψ t) M (χ t n) (P t) n.1 (hJT ht).1
        (hχ t ht n) (hP t ht) (sphere_norm n))
    exact hh.trans (by
      have hh' := mul_le_mul_of_nonneg_right (hJT ht).2
        (show 0≤C*|ψ t| *M*(4*Real.pi) by positivity)
      nlinarith)
  have hi := hψ.abs.const_mul (C*(4*Real.pi)*T*M)
  have hh := norm_integral_le_of_norm_le hi (ae_restrict_of_forall_mem hJ hpoint)
  rw [integral_const_mul] at hh
  exact hh

end RVM

end

end OAI
