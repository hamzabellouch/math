import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.BoundedPlanarResidue

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open MeasureTheory

 theorem radialEndProbability_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) {p : Radial.Plane}
    (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) (i : TrapezoidWeight A B) :
    ContDiffAt ℝ ∞ (fun z => radialEndProbability Radial.latticeIndex D m p ε z i) y :=
  ((radialProbability_smooth hA hAB D m hp i).contMDiffAt.comp y
    ((infinityDiffeomorph (parameters 0) ε).contMDiffOn.contMDiffAt
      ((infinityDiffeomorph (parameters 0) ε).open_source.mem_nhds hy))).contDiffAt

 theorem radialEndRegularPrimitive_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ)
    (c : ℝ) {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (radialEndRegularPrimitive Radial.latticeIndex D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (radialEndProbability_contDiffAt hA hAB D m hp ε hy i).smul
    (weightedRegularEndPrimitive_contDiffAt (D i) (m i) ε c hR))

 theorem radialEndResidue_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ)
    (c : ℝ) {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source) :
    ContDiffAt ℝ ∞ (radialEndResidue Radial.latticeIndex D m c p ε) y :=
  ContDiffAt.sum (fun i _ => (radialEndProbability_contDiffAt hA hAB D m hp ε hy i).mul contDiffAt_const)

local instance cubicRadialEndSmoothSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

 theorem tendsto_radial_cubic_cutoff_mass {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0<R) (hR1 : R<1)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)) := by
  obtain ⟨Mlog,hMlog,hlog⟩ := exists_regularCoefficient_log_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) hR
  obtain ⟨M,hM,hbound⟩ := exists_regularPrimitive_bound
    (cubicDegree D (A := A) (B := B)) (cubicMarkedOrder S) c hR
  obtain ⟨K,hK⟩ := (hg.continuous_deriv (by simp)).bounded_above_of_compact_support hgc.deriv
  have hK0 : 0≤K := (norm_nonneg (deriv g 0)).trans (hK 0)
  have hKg (t : ℝ) : |deriv g t|≤K := by simpa only [Real.norm_eq_abs] using hK t
  have hpoint (ε : EndIndex) (n : ℕ) (y : Plane)
      (hy : y∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))) :
      y∈(infinityDiffeomorph (parameters 0) ε).source ∧
      Complex.equivRealProdCLM.symm y∈endRegularRegion ∧
      y∈radialAnnulus 0 R ∧ 0<radiusSq y ∧ radiusSq y<1 := by
    have hn : 1≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hys : y∈radialAnnulus 0 R := ⟨radiusSq_nonneg _,hy.2.trans (div_le_self hRp.le hn)⟩
    have hxR : Complex.equivRealProdCLM.symm y∈endRegularRegion := by
      apply hR
      change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
      rw [radiusSq_complex]
      exact hys.2
    have hRI : {s : ℂ | Complex.normSq s≤R/((n:ℝ)+1)}⊆infinityRegion (parameters 0) :=
      fun s hs => (hR (hs.trans (div_le_self hRp.le hn))).1
    exact ⟨radialAnnulus_in_end (parameters 0) (div_pos hr (by positivity)) hRI ε hy,
      hxR,hys,(div_pos hr (by positivity)).trans_le hy.1,hys.2.trans_lt hR1⟩
  have ht := tendsto_curveCutoff_bounded_residue (parameters 0)
    (radialPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialPrimitive_smooth hA hAB _ _ c hp)
    (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialForm_smooth hA hAB _ _ c hp) (radialForm_skew _ _ _ c p) rfl
    hg hgc hr hRp.le (fun s hs => (hR hs).1) h1 h0 hK0 hM hKg
    (fun ε => c*limitingEndOrder D S (planeVector p.1 p.2) ε)
    (logarithmicError (|c| * (2*Mlog+Fintype.card (TrapezoidWeight A B))) R)
    (fun n => logarithmicError_nonneg (by positivity) hRp hR1 n)
    (tendsto_logarithmicError hRp _)
    (radialEndRegularPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)
    (fun ε n y hy => (radialEndRegularPrimitive_contDiffAt hA hAB _ _ c hp ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1).continuousAt.continuousWithinAt)
    (fun ε n y hy => (radialEndResidue_contDiffAt hA hAB _ _ c hp ε
      (hpoint ε n y hy).1).continuousAt.continuousWithinAt)
    (fun ε n y hy => radialEndRegularPrimitive_norm_le (Radial.lattice_zero A B) _ _ c p ε y
      (fun k => hbound k ε y (hpoint ε n y hy).2.2.1))
    (fun ε n y hy => by
      have hh := radialEndResidue_error hA hS0 hAB hSB hB hS hp ε
        (hpoint ε n y hy).1 (hpoint ε n y hy).2.1
        (hpoint ε n y hy).2.2.2.1 (hpoint ε n y hy).2.2.2.2 hMlog
        (fun k => hlog k ε y (hpoint ε n y hy).2.2.1) c
      apply hh.trans
      rw [←mul_div_assoc]
      exact logarithmicError_bound (by positivity) hRp hR1 n (hpoint ε n y hy).2.2.2.1 hy.2)
    (fun ε n y hy => radialPrimitive_infinity
      (Radial.latticeIndex (A := A) (B := B)) (fun k => (cubicMarked_lt_degree hB hS k).le)
      (fun k => cubicMarked_twice_complement hB hS k) c p ε
      (hpoint ε n y hy).1 (hpoint ε n y hy).2.1)
  rw [←Finset.mul_sum] at ht
  rw [sum_limitingEndOrder] at ht
  exact ht

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

def latticeOrigin (A B : ℕ) : TrapezoidWeight A B :=
  ⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩

theorem latticeIndex_injective (A B : ℕ) : Injective (latticeIndex (A:=A) (B:=B)) := by
  intro i j h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

theorem monomial_origin (k : ℕ × ℕ) : monomial k (0,0)=if k=(0,0) then 1 else 0 := by
  classical
  by_cases h0 : k.1=0 <;> by_cases h1 : k.2=0
  · have hk : k=(0,0) := Prod.ext h0 h1
    simp [hk,monomial]
  · have hk : k≠(0,0) := fun h => h1 (congrArg Prod.snd h)
    simp [monomial,h0,h1,hk]
  · have hk : k≠(0,0) := fun h => h0 (congrArg Prod.fst h)
    simp [monomial,h0,h1,hk]
  · have hk : k≠(0,0) := fun h => h0 (congrArg Prod.fst h)
    simp [monomial,h0,h1,hk]

theorem lattice_monomial_origin {A B : ℕ} (i : TrapezoidWeight A B) :
    monomial (latticeIndex i) (0,0)=if i=latticeOrigin A B then 1 else 0 := by
  rw [monomial_origin]
  have he : latticeIndex i=(0,0) ↔ i=latticeOrigin A B :=
    ⟨fun h => latticeIndex_injective A B h,fun h => by simp [h,latticeOrigin,latticeIndex]⟩
  simp only [he]

theorem lattice_polynomial_origin {A B : ℕ} (a : TrapezoidWeight A B → ℝ) :
    polynomial latticeIndex a (0,0)=a (latticeOrigin A B) := by
  classical
  simp [polynomial,lattice_monomial_origin]

theorem lattice_probability_origin {A B : ℕ} {a : TrapezoidWeight A B → ℝ}
    (ha : 0<a (latticeOrigin A B)) (i : TrapezoidWeight A B) :
    probability latticeIndex a (0,0) i=if i=latticeOrigin A B then 1 else 0 := by
  rw [probability,lattice_monomial_origin,lattice_polynomial_origin]
  split_ifs with hi
  · subst i
    simp [ha.ne']
  · simp

theorem lattice_selected_origin {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) (i : TrapezoidWeight A B) :
    selected latticeIndex a (0,0) i=if i=latticeOrigin A B then 1 else 0 := by
  have hi := nonnegativeInverse_of_moment ha (lattice_zero A B)
    (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) (r:=(0,0)) ⟨le_rfl,le_rfl⟩
  rw [moment_origin] at hi
  rw [selected,hi]
  exact lattice_probability_origin (ha _) i

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section

variable {ι : Type*} [Fintype ι]

theorem radialPrimitive_swap {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    (D m : ι → ℕ) (c : ℝ) {p : Radial.Plane}
    (hp : ∀ x : BaseCurve,∃ r : Radial.Plane,(0≤r.1 ∧ 0≤r.2) ∧
      Radial.moment k (fun j => coefficientNorm (D j) (m j) x) r=p) :
    radialPrimitive (fun j => (k j).swap) D m c p.swap=radialPrimitive k D m c p := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [radialProbability,Radial.selected_swap
    (fun j => coefficientNorm_pos (D j) (m j) x) h0 he0 he1 (hp x)]
  rfl

theorem radialPrimitive_origin {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D m : TrapezoidWeight A B → ℕ) (c : ℝ) :
    radialPrimitive Radial.latticeIndex D m c (0,0)=
      weightedFSPrimitive (D (Radial.latticeOrigin A B)) (m (Radial.latticeOrigin A B)) c := by
  classical
  funext x
  simp only [radialPrimitive,radialProbability,Radial.lattice_selected_origin hA hAB
    (fun j => coefficientNorm_pos (D j) (m j) x)]
  simp

theorem radialForm_face_positive {k : ι → ℕ × ℕ}
    (h0 : ∃ i,k i=(0,0)) (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1))
    {D m : ι → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0<c)
    {p : ℝ} (hp : Surrounds (Radial.faceWeight k) p) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (radialForm k D m c (0,p)) b y (1,0) (0,1) := by
  obtain ⟨i0,hi0⟩ := h0
  let : Nonempty (Radial.Face k) := ⟨⟨i0,by simp [hi0]⟩⟩
  rw [radialForm,radialPrimitive_eq_face ⟨i0,hi0⟩ he0 he1 D m c hp]
  have hh := selectedForm_positive (D := fun i : Radial.Face k => D i.val)
    (m := fun i : Radial.Face k => m i.val) (fun i => hm i.val) hc hp b hy
  exact hh

theorem radialForm_positive {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {D m : TrapezoidWeight A B → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0<c)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0<chartTwoForm (radialForm Radial.latticeIndex D m c p) b y (1,0) (0,1) := by
  have h0 := Radial.lattice_zero A B
  have he0 := Radial.lattice_unit_fst hA hAB
  have he1 := Radial.lattice_unit_snd hA hAB
  by_cases hp0 : p.1=0
  · by_cases hp1 : p.2=0
    · have he : p=(0,0) := Prod.ext hp0 hp1
      rw [he,radialForm,radialPrimitive_origin hA hAB,weightedFSPrimitive_exterior]
      exact weightedFSForm_positive (hm _) hc b hy
    · have hpos : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1)
      have he : p=(0,p.2) := Prod.ext hp0 rfl
      rw [he]
      apply radialForm_face_positive h0 he0 he1 hm hc _ b hy
      exact Radial.face_surrounds h0 (Radial.lattice_end_snd A B)
        ⟨hpos,by simpa [hp0] using hp.2.2.2⟩
  · have hpos : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    by_cases hp1 : p.2=0
    · have h0' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,0) := by
        obtain ⟨i,hi⟩ := h0; exact ⟨i,by simp [hi]⟩
      have he0' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(1,0) := by
        obtain ⟨i,hi⟩ := he1; exact ⟨i,by simp [hi]⟩
      have he1' : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,1) := by
        obtain ⟨i,hi⟩ := he0; exact ⟨i,by simp [hi]⟩
      have hend : ∃ i : TrapezoidWeight A B,(Radial.latticeIndex i).swap=(0,A) := by
        obtain ⟨i,hi⟩ := Radial.lattice_end_fst hAB; exact ⟨i,by simp [hi]⟩
      rw [radialForm,←radialPrimitive_swap h0 he0 he1 D m c
        (fun x => Radial.trapezoid_radial_surjective hAB
          (fun j => coefficientNorm_pos (D j) (m j) x) hp)]
      have he : p.swap=(0,p.1) := Prod.ext hp1 rfl
      rw [he]
      exact radialForm_face_positive h0' he0' he1' hm hc
        (Radial.face_surrounds h0' hend ⟨hpos,hp.2.1⟩) b hy
    · let : Nonempty (TrapezoidWeight A B) := ⟨Radial.latticeOrigin A B⟩
      have hs : Surrounds (Radial.weight Radial.latticeIndex) (planeVector p.1 p.2) :=
        trapezoidWeight_surrounds hAB ⟨hpos,hp.2.1,lt_of_le_of_ne hp.2.2.1 (Ne.symm hp1),hp.2.2.2⟩
      rw [radialForm,radialPrimitive_eq_reduced h0 he0 he1 D m c hs]
      exact reducedForm_positive hm hc hs b hy

end

def regularEndPhase (ε : EndIndex) (y : Plane) : PlanePhase HomogeneousIndex :=
  complexCartesian (endRegular ε (Complex.equivRealProdCLM.symm y))

def regularEndPrimitive (ε : EndIndex) (c : ℝ) : Plane → Plane →L[ℝ] ℝ :=
  staticPullbackOneForm (hopfPrimitive c) (regularEndPhase ε)

def endResidue (ε : EndIndex) (c : ℝ) : ℝ := if ε=zeroEnd then 0 else c

 theorem regularEndPhase_contDiffAt (ε : EndIndex) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (regularEndPhase ε) y :=
  (complexCartesian (ι := HomogeneousIndex)).contDiff.contDiffAt.comp y
    (((endRegular_contDiffAt ε hy).restrict_scalars ℝ).comp y
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

 theorem regularEndPrimitive_contDiffAt (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    ContDiffAt ℝ ∞ (regularEndPrimitive ε c) y :=
  staticPullbackOneForm_smoothAt
    (hopfPrimitive_smoothAt c (endRegular_cartesian_ne_zero ε _))
    (regularEndPhase_contDiffAt ε hy)

 theorem endRegular_scale {ε : EndIndex} (hε : ε≠zeroEnd) {s : ℂ} (hs : s≠0) :
    endRegular ε s=s•complexAffineLift (endQuotient ε s) := by
  rw [endQuotient_homogeneous hε hs,smul_smul,mul_inv_cancel₀ hs,one_smul]

 theorem endQuotientPrimitive_residue (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (h0 : Complex.equivRealProdCLM.symm y≠0) (v : Plane) :
    affineFSPrimitive c (complexCartesian (endQuotient ε (Complex.equivRealProdCLM.symm y)))
      (fderiv ℝ (fun z : Plane => complexCartesian
        (endQuotient ε (Complex.equivRealProdCLM.symm z))) y v)=
      regularEndPrimitive ε c y v-(endResidue ε c/2)*angularOneForm y v := by
  let Q : Plane → AffineIndex → ℂ := fun z => endQuotient ε (Complex.equivRealProdCLM.symm z)
  have hQ : DifferentiableAt ℝ Q y :=
    (((endQuotient_contDiffAt ε ⟨h0,hy.1⟩).restrict_scalars ℝ).differentiableAt (by simp)).comp y
      Complex.equivRealProdCLM.symm.differentiableAt
  have hp := affineFSPrimitive_hopf_pullback hQ c v
  change _ =_ at hp
  have hN : complexCartesian (complexAffineLift (Q y))≠0 := by
    intro hz
    have hf : complexAffineLift (Q y)=0 := by
      apply (complexCartesian (ι := HomogeneousIndex)).injective
      simpa only [map_zero] using hz
    exact one_ne_zero (congrFun hf none)
  by_cases hε : ε=zeroEnd
  · have he : regularEndPhase ε=ᶠ[𝓝 y] fun z => complexCartesian (complexAffineLift (Q z)) := by
      have hR := endRegularRegion_open.preimage Complex.equivRealProdCLM.symm.continuous
      have hZ := (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds h0
      filter_upwards [hR.mem_nhds hy,hZ] with z hz hz0
      simp only [regularEndPhase,endRegular,ite_eq_left hε]
      congr 2
      exact (endQuotient_zeroEnd hz0 hz).symm.trans (congrArg (fun ε => endQuotient ε _) hε.symm)
    change _=hopfPrimitive c (regularEndPhase ε y) (fderiv ℝ (regularEndPhase ε) y v)-_
    rw [he.eq_of_nhds,he.fderiv_eq]
    rw [show endResidue ε c=0 from ite_eq_left hε]
    simpa only [zero_div,zero_mul,sub_zero] using hp.symm
  · have he : regularEndPhase ε=ᶠ[𝓝 y] fun z => complexCartesian
        ((Complex.equivRealProdCLM.symm z)•complexAffineLift (Q z)) := by
      filter_upwards [(isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds h0]
        with z hz
      exact congrArg complexCartesian (endRegular_scale hε hz)
    have hG : DifferentiableAt ℝ (fun z => complexAffineLift (Q z)) y :=
      (complexAffineLift_smooth.differentiable (by simp) _).comp y hQ
    have hg := hopfPrimitive_variable_gauge Complex.equivRealProdCLM.symm.differentiableAt
      hG h0 hN c v
    change _=hopfPrimitive c (regularEndPhase ε y) (fderiv ℝ (regularEndPhase ε) y v)-_
    rw [he.eq_of_nhds,he.fderiv_eq,hg,hp,show endResidue ε c=c from ite_eq_right hε]
    rw [ContinuousLinearEquiv.fderiv]
    simp only [ContinuousLinearEquiv.coe_coe]
    have hns : Complex.normSq (Complex.equivRealProdCLM.symm y)=radiusSq y := by
      change y.1*y.1+y.2*y.2=y.1^2+y.2^2
      ring
    have hca : complexArea (Complex.equivRealProdCLM.symm y)
        (Complex.equivRealProdCLM.symm v)=planarArea y v := by
      rw [complexArea_apply]
      rfl
    rw [hns,hca]
    simp only [angularOneForm,smul_apply,smul_eq_mul]
    ring

 theorem cubic_curveFSPrimitive_infinity (ε : EndIndex) (c : ℝ) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion) :
    euclideanPullbackOneForm (fun _ => curveFSPrimitive c)
      (infinityDiffeomorph (parameters 0) ε) (0,y)=
      regularEndPrimitive ε c y-(endResidue ε c/2) • angularOneForm y := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain (parameters 0) := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hg := cubic_infinityPhase_germ ε hy
  change euclideanPullbackOneForm (fun _ => manifoldPullbackOneForm
    (fun _ => affineFSPrimitive c) phaseInclusion 0) (infinityDiffeomorph (parameters 0) ε) (0,y)=_
  rw [euclideanPullbackOneForm_comp (phaseInclusion_smooth.mdifferentiable (by simp) _)
    ((infinityDiffeomorph (parameters 0) ε).mdifferentiableAt (by simp) hy)]
  apply ContinuousLinearMap.ext
  intro v
  change affineFSPrimitive c ((phaseInclusion ∘ infinityDiffeomorph (parameters 0) ε) y)
    (manifoldMapDifferential (E := PlanePhase AffineIndex) (F := Plane)
      (phaseInclusion ∘ infinityDiffeomorph (parameters 0) ε) y v)=_
  rw [manifoldMapDifferential,mfderiv_eq_fderiv,hg.eq_of_nhds,hg.fderiv_eq]
  exact endQuotientPrimitive_residue ε c hR hD.1 v

 theorem sum_endResidue (c : ℝ) : (∑ ε : EndIndex,endResidue ε c)=3*c := by
  have h (ε : EndIndex) : endResidue ε c=c-(if ε=zeroEnd then c else 0) := by
    by_cases he : ε=zeroEnd <;> simp [endResidue,he]
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  norm_num [EndIndex,Fintype.card_fun]
  ring

theorem exists_regularEndPrimitive_extension {R : ℝ}
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion) (ε : EndIndex) (c : ℝ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ,ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] regularEndPrimitive ε c := by
  let U : Set Plane := Complex.equivRealProdCLM.symm ⁻¹' endRegularRegion
  have hU : IsOpen U := endRegularRegion_open.preimage Complex.equivRealProdCLM.symm.continuous
  have hKU : radialAnnulus 0 R⊆U := by
    intro y hy
    apply hR
    change Complex.normSq (Complex.equivRealProdCLM.symm y)≤R
    rw [radiusSq_complex]
    exact hy.2
  have hf : ContDiffOn ℝ ∞ (regularEndPrimitive ε c) U :=
    fun y hy => (regularEndPrimitive_contDiffAt ε c hy).contDiffWithinAt
  obtain ⟨χ,_hχ,_hχc,_hχU,_hr,_h1,hf,hc,he⟩ :=
    exists_smooth_compact_extension (radialAnnulus_compact 0 R) hU hKU hf
  exact ⟨fun y => χ y • regularEndPrimitive ε c y,hf,hc,he⟩

theorem cubic_regular_extension_germ {R : ℝ} {ε : EndIndex} {c : ℝ}
    {β : Plane → Plane →L[ℝ] ℝ}
    (he : β=ᶠ[𝓝ˢ (radialAnnulus 0 R)] regularEndPrimitive ε c)
    {z : Plane} (hz : radiusSq z≤R) : β=ᶠ[𝓝 z] regularEndPrimitive ε c :=
  he.filter_mono (nhds_le_nhdsSet ⟨radiusSq_nonneg z,hz⟩)

end PackingSufficiencySupport.CubicModel
end

end OAI
