import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularHandleDensity

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def surfaceSuspensionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  p.1.1 * Φ.hamiltonian (p.1.1*S p.2,Φ.map (p.1.1*S p.2) p.1.2)

def surfaceFirstCorrectionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : V → ℝ) (p : (ℝ × V) × ℝ) : ℝ :=
  S p.2 * (H ((Φ.map p.1.1).symm (Φ.map (p.1.1*S p.2) p.1.2))-H p.1.2)

@[fun_prop] theorem surfaceSuspensionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (surfaceSuspensionCoefficient Φ S) := by
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => p.1.1*S p.2) :=
    (contDiff_fst.comp contDiff_fst).mul (hS.comp contDiff_snd)
  have hq := Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_fst))
  exact (contDiff_fst.comp contDiff_fst).mul (Φ.hamiltonian_smooth.comp (ht.prodMk hq))

@[fun_prop] theorem surfaceFirstCorrectionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {H : V → ℝ} (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (surfaceFirstCorrectionCoefficient Φ S H) := by
  have ht : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => p.1.1*S p.2) :=
    (contDiff_fst.comp contDiff_fst).mul (hS.comp contDiff_snd)
  have hq := Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_fst))
  exact (hS.comp contDiff_snd).mul
    ((hH.comp (Φ.inverse_smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk hq))).sub
      (hH.comp (contDiff_snd.comp contDiff_fst)))

@[simp] theorem surfaceSuspensionCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (v : V) (s : ℝ) : surfaceSuspensionCoefficient Φ S ((0,v),s)=0 := by
  simp [surfaceSuspensionCoefficient]

@[simp] theorem surfaceFirstCorrectionCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (H : V → ℝ) (v : V) (s : ℝ) :
    surfaceFirstCorrectionCoefficient Φ S H ((0,v),s)=0 := by
  simp [surfaceFirstCorrectionCoefficient,Φ.zero]

theorem surfaceFirstCorrectionCoefficient_tails (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (H : V → ℝ) (p : ℝ × V) (s : ℝ) (hs : S s=0 ∨ S s=1) :
    surfaceFirstCorrectionCoefficient Φ S H (p,s)=0 := by
  rcases hs with hs|hs <;> simp [surfaceFirstCorrectionCoefficient,hs]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def handleFirstCorrection
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
      (p,(D.chart.symm x).1) • D.radial b x +
  surfaceFirstCorrectionCoefficient Φ (intervalClock (-b) b) H
      (p,(D.chart.symm x).1) • D.dual x

def globalSurfaceFirstPrimitive
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  Γ p.2 + extendManifoldOneForm D.chart.target
    (handleFirstCorrection D b Φ H p)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem handleFirstCorrection_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (p : ℝ × V) {x : M}
    (hx : x∈D.chart.target) (hn : x∉D.chart '' band b) :
    handleFirstCorrection D b Φ H p x=0 := by
  have hr : D.radial b x=0 :=
    D.radial_zero hb hn
  have ht : intervalClock (-b) b (D.chart.symm x).1=0 ∨
      intervalClock (-b) b (D.chart.symm x).1=1 := by
    have hs := D.off_band_inverse b hx hn
    simp only [mem_Icc,not_and_or,not_le] at hs
    rcases hs with hs|hs
    · exact Or.inl (intervalClock_zero (by linarith) hs.le)
    · exact Or.inr (intervalClock_one (by linarith) hs.le)
  simp only [handleFirstCorrection,hr,smul_zero,
    surfaceFirstCorrectionCoefficient_tails Φ _ H p _ ht,zero_smul,add_zero]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem globalSurfaceFirstPrimitive_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b)
    (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ) (Γ : V → ManifoldOneForm E M)
    (p : ℝ × V) {x : M} (hn : x∉D.chart '' band b) :
    globalSurfaceFirstPrimitive D b Φ H Γ p x=Γ p.2 x := by
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,
      handleFirstCorrection_off_band D hb Φ H p hx hn]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem globalSurfaceFirstPrimitive_zero
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceFirstPrimitive D b Φ H Γ (0,v)=Γ v := by
  funext x
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_inside hx,handleFirstCorrection]
  · simp [globalSurfaceFirstPrimitive,extendManifoldOneForm_outside hx]

theorem globalSurfaceFirstPrimitive_smooth [T2Space M]
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {H : V → ℝ} (hH : ContDiff ℝ ∞ H)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceFirstPrimitive D b Φ H Γ) := by
  have hr := D.radial_smooth hb hbw
  have hβ := D.dual_smooth
  have hα := extendManifoldOneForm_smooth D.chart.open_target
    (D.image_band_compact hbw).isClosed
    (D.image_band_subset_target hbw)
    (α := handleFirstCorrection D b Φ H)
    (fun c => by
      have h1 := annular_coefficient_smooth_on D.chart.open_target
        (annular_inverse_fst_smooth D.chart)
        (surfaceSuspensionCoefficient_smooth Φ (intervalClock_smooth (-b) b))
        (α := D.radial b) (fun c => (hr c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      have h2 := annular_coefficient_smooth_on D.chart.open_target
        (annular_inverse_fst_smooth D.chart)
        (surfaceFirstCorrectionCoefficient_smooth Φ (intervalClock_smooth (-b) b) hH)
        (α := D.dual) (fun c => (hβ c).comp
          (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hy => ⟨mem_univ _,hy⟩)) c
      simpa only [handleFirstCorrection,chartOneForm,ContinuousLinearMap.add_comp] using h1.add h2)
    (fun p x hx hn => handleFirstCorrection_off_band D hb Φ H p hx hn)
  intro c
  have hmap : ContDiffOn ℝ ∞ (fun q : (ℝ × V) × E => (q.1.2,q.2))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) :=
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
  have hbg := (hΓ c).comp hmap (fun _ hq => ⟨mem_univ _,hq.2⟩)
  simpa only [globalSurfaceFirstPrimitive,chartOneForm_add,Function.comp_apply] using hbg.add (hα c)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

def surfaceSecondCorrectionCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ p.1.1
    (p.2,Φ.map (S p.2) p.1.2) - S p.2*H p.1.2 - p.1.1*(K p.1.2-H p.1.2)

def surfaceSecondExtraCoefficient (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : (ℝ × V) × ℝ) : ℝ :=
  surfaceSecondCorrectionCoefficient Φ S K H h ρ ρ₀ p -
    surfaceFirstCorrectionCoefficient Φ S H ((1,p.1.2),p.2)

theorem surfaceSecondCorrectionCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {K H : V → ℝ} {h : ι → V → ℝ} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i,ContDiff ℝ ∞ (h i)) (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) :
    ContDiff ℝ ∞ (surfaceSecondCorrectionCoefficient Φ S K H h ρ ρ₀) := by
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × V) × ℝ => (p.2,Φ.map (S p.2) p.1.2)) :=
    contDiff_snd.prodMk (Φ.smooth.comp ((hS.comp contDiff_snd).prodMk
      (contDiff_snd.comp contDiff_fst)))
  have h1 := (surfaceFirstLayer_smooth hS hH (Φ.map_inverse_smooth 1)).comp hp
  have h2 := (surfaceFinalLayer_smooth (hK.sub hH)
    (surfaceRemainder_smooth hK hH hh (Φ.map_inverse_smooth 1)) hh hρ hρ₀).comp hp
  exact ((((contDiff_const.sub (contDiff_fst.comp contDiff_fst)).mul h1).add
    ((contDiff_fst.comp contDiff_fst).mul h2)).sub
    ((hS.comp contDiff_snd).mul (hH.comp (contDiff_snd.comp contDiff_fst)))).sub
    ((contDiff_fst.comp contDiff_fst).mul ((hK.sub hH).comp (contDiff_snd.comp contDiff_fst)))

theorem surfaceSecondExtraCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {K H : V → ℝ} {h : ι → V → ℝ} {ρ : ι → ℝ → ℝ} {ρ₀ : ℝ → ℝ}
    (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K) (hH : ContDiff ℝ ∞ H)
    (hh : ∀ i,ContDiff ℝ ∞ (h i)) (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    (hρ₀ : ContDiff ℝ ∞ ρ₀) :
    ContDiff ℝ ∞ (surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀) :=
  (surfaceSecondCorrectionCoefficient_smooth Φ hS hK hH hh hρ hρ₀).sub
    ((surfaceFirstCorrectionCoefficient_smooth Φ hS hH).comp
      ((contDiff_const.prodMk (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd))

@[simp] theorem surfaceSecondExtraCoefficient_zero (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (v : V) (s : ℝ) : surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ ((0,v),s)=0 := by
  simp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient,
    surfaceFirstCorrectionCoefficient,surfaceInterpolatedLayer,surfaceFirstLayer,
    sub_zero,zero_mul,one_mul,add_zero]
  ring

theorem surfaceSecondExtraCoefficient_tails (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : ℝ × V) (s : ℝ)
    (hs : (S s=0 ∧ (∀ i,ρ i s=0) ∧ ρ₀ s=0) ∨
      (S s=1 ∧ (∀ i,ρ i s=1) ∧ ρ₀ s=1)) :
    surfaceSecondExtraCoefficient Φ S K H h ρ ρ₀ (p,s)=0 := by
  have he := surfaceInterpolatedLayer_endpoints Φ S K H h ρ ρ₀ p.1 s p.2
  rcases hs with ⟨hs,hρ,hρ₀⟩|⟨hs,hρ,hρ₀⟩
  · dsimp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient]
    rw [he.1 hs hρ hρ₀,surfaceFirstCorrectionCoefficient_tails Φ S H (1,p.2) s (Or.inl hs),hs]
    ring
  · dsimp only [surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient]
    rw [he.2 hs hρ hρ₀,surfaceFirstCorrectionCoefficient_tails Φ S H (1,p.2) s (Or.inr hs),hs]
    ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ} {ι : Type*} [Fintype ι]

def handleSecondExtra
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (p : ℝ × V) : ManifoldOneForm E M := fun x =>
  surfaceSecondExtraCoefficient Φ (intervalClock (-b) b) K H h ρ ρ₀
    (p,(D.chart.symm x).1) • D.dual x

def globalSurfaceSecondPrimitive
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) : ManifoldOneForm E M :=
  globalSurfaceFirstPrimitive D b Φ H Γ (1,p.2) +
    (p.1*(K p.2-H p.2)) • D.dual +
    extendManifoldOneForm D.chart.target
      (handleSecondExtra D b Φ K H h ρ ρ₀ p)

@[simp] theorem globalSurfaceSecondPrimitive_zero
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (v : V) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (0,v)=
      globalSurfaceFirstPrimitive D b Φ H Γ (1,v) := by
  funext x
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,handleSecondExtra]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx]

theorem handleSecondExtra_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (p : ℝ × V) {x : M} (hx : x∈D.chart.target)
    (hn : x∉D.chart '' band b) : handleSecondExtra D b Φ K H h ρ ρ₀ p x=0 := by
  have hs := D.off_band_inverse b hx hn
  simp only [mem_Icc,not_and_or,not_le] at hs
  have ht : (intervalClock (-b) b (D.chart.symm x).1=0 ∧
      (∀ i,ρ i (D.chart.symm x).1=0) ∧
      ρ₀ (D.chart.symm x).1=0) ∨
    (intervalClock (-b) b (D.chart.symm x).1=1 ∧
      (∀ i,ρ i (D.chart.symm x).1=1) ∧
      ρ₀ (D.chart.symm x).1=1) := by
    rcases hs with hs|hs
    · exact Or.inl ⟨intervalClock_zero (by linarith) hs.le,hlo _ hs.le⟩
    · exact Or.inr ⟨intervalClock_one (by linarith) hs.le,hhi _ hs.le⟩
  simp only [handleSecondExtra,surfaceSecondExtraCoefficient_tails Φ _ K H h ρ ρ₀ p _ ht,zero_smul]

theorem globalSurfaceSecondPrimitive_off_band
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    (Γ : V → ManifoldOneForm E M) (p : ℝ × V) {x : M}
    (hn : x∉D.chart '' band b) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ p x=
      Γ p.2 x+(p.1*(K p.2-H p.2)) • D.dual x := by
  by_cases hx : x∈D.chart.target
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_inside hx,
      handleSecondExtra_off_band D hb Φ K H h ρ ρ₀ hlo hhi p hx hn,
      globalSurfaceFirstPrimitive_off_band D hb Φ H Γ (1,p.2) hn]
  · simp [globalSurfaceSecondPrimitive,extendManifoldOneForm_outside hx,
      globalSurfaceFirstPrimitive_off_band D hb Φ H Γ (1,p.2) hn]

variable [IsManifold 𝓘(ℝ,E) ∞ M]
theorem globalSurfaceSecondPrimitive_smooth [T2Space M]
    (D : AnnularHandleData E M)
    {b : ℝ} (hb : 0<b) (hbw : b<D.width)
    (Φ : CompactHamiltonianIsotopy Ω) {K H : V → ℝ} (hK : ContDiff ℝ ∞ K)
    (hH : ContDiff ℝ ∞ H) {h : ι → V → ℝ} (hh : ∀ i,ContDiff ℝ ∞ (h i))
    {ρ : ι → ℝ → ℝ} (hρ : ∀ i,ContDiff ℝ ∞ (ρ i))
    {ρ₀ : ℝ → ℝ} (hρ₀ : ContDiff ℝ ∞ ρ₀)
    (hlo : ∀ s, s ≤ -b → (∀ i,ρ i s=0) ∧ ρ₀ s=0)
    (hhi : ∀ s, b ≤ s → (∀ i,ρ i s=1) ∧ ρ₀ s=1)
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ) :
    SmoothOneFormFamily (globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ) := by
  have hβ := D.dual_smooth
  have hα := extendManifoldOneForm_smooth D.chart.open_target
    (D.image_band_compact hbw).isClosed
    (D.image_band_subset_target hbw)
    (α := handleSecondExtra D b Φ K H h ρ ρ₀)
    (fun c => annular_coefficient_smooth_on D.chart.open_target
      (annular_inverse_fst_smooth D.chart)
      (surfaceSecondExtraCoefficient_smooth Φ (intervalClock_smooth (-b) b) hK hH hh hρ hρ₀)
      (α := D.dual) (fun c => (hβ c).comp
        (f := fun y => ((0:ℝ),y)) (contDiffOn_const.prodMk contDiffOn_id)
        (fun _ hy => ⟨mem_univ _,hy⟩)) c)
    (fun p x hx hn => handleSecondExtra_off_band D hb Φ K H h ρ ρ₀ hlo hhi p hx hn)
  have hfirst := (globalSurfaceFirstPrimitive_smooth D hb hbw Φ hH hΓ).comp
    (f := fun p : ℝ × V => (1,p.2)) (contDiff_const.prodMk (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × V → V)))
  have hj := (hβ.comp (f := fun _ : ℝ × V => (0:ℝ)) contDiff_const).smul
    (contDiff_fst.mul ((hK.sub hH).comp contDiff_snd))
  exact (hfirst.add hj).add hα

end
section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

theorem globalSurfaceFirstPrimitive_normal
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) (p : ℝ × V)
    {x : M} (hx : x∈D.chart.target)
    (hN : Γ p.2 x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p.2) • D.dual x) :
    globalSurfaceFirstPrimitive D b Φ H Γ p x=
      γ x+surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
        (p,(D.chart.symm x).1) • D.radial b x+
      (intervalClock (-b) b (D.chart.symm x).1*
        H ((Φ.map p.1).symm (Φ.map (p.1*intervalClock (-b) b
          (D.chart.symm x).1) p.2))) • D.dual x := by
  simp only [globalSurfaceFirstPrimitive,Pi.add_apply,extendManifoldOneForm_inside hx,hN,
    handleFirstCorrection,surfaceFirstCorrectionCoefficient]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem globalSurfaceSecondPrimitive_normal {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M) (p : ℝ × V)
    {x : M} (hx : x∈D.chart.target)
    (hN : Γ p.2 x=γ x+
      (intervalClock (-b) b (D.chart.symm x).1*H p.2) • D.dual x) :
    globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ p x=
      γ x+surfaceSuspensionCoefficient Φ (intervalClock (-b) b)
        ((1,p.2),(D.chart.symm x).1) • D.radial b x+
      surfaceInterpolatedLayer (intervalClock (-b) b) K H h (Φ.map 1).symm ρ ρ₀ p.1
        ((D.chart.symm x).1,
          Φ.map (intervalClock (-b) b (D.chart.symm x).1) p.2) •
        D.dual x := by
  simp only [globalSurfaceSecondPrimitive,globalSurfaceFirstPrimitive,Pi.add_apply,Pi.smul_apply,
    extendManifoldOneForm_inside hx,hN,handleFirstCorrection,handleSecondExtra,
    surfaceSecondExtraCoefficient,surfaceSecondCorrectionCoefficient,
    surfaceFirstCorrectionCoefficient,one_mul]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

end
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 def handleAnnularCover
    (D : AnnularHandleData E M)
    : Plane → M := D.chart ∘ cylinderCover

 theorem handleAnnularCover_smoothAt
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ (D.handleAnnularCover) q :=
  (D.chart.contMDiffOn.contMDiffAt
    (D.chart.open_source.mem_nhds hq)).comp q cylinderCover_smooth.contMDiffAt

 theorem handleAnnularCover_derivative
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q=
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) :=
  mfderiv_comp q (D.chart.mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))

 theorem dual_cover
    (D : AnnularHandleData E M)
    {q : Plane}
    (hq : cylinderCover q∈D.chart.source) (v : Plane) :
    D.dual (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=D.clock (circleTurn q.2)*v.2 := by
  rw [D.handleAnnularCover_derivative hq]
  change D.dual (D.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [D.dual_pullback _ hq,cylinderCover_derivative]
  exact congrArg (D.clock (circleTurn q.2)*·) (circleAngular_unit_pullback q.2 v.2)

 theorem radial_cover
    (D : AnnularHandleData E M)
    (b : ℝ) {q : Plane} (hq : cylinderCover q∈D.chart.source)
    (v : Plane) :
    D.radial b (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=
      deriv (intervalClock (-b) b) q.1*v.1 := by
  rw [D.handleAnnularCover_derivative hq]
  change D.radial b (D.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [D.radial_pullback b hq,cylinderCover_derivative]
  rfl

 theorem handleAnnularCover_inverse
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    D.chart.symm (D.handleAnnularCover q)=cylinderCover q :=
  D.chart.left_inv hq

end

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularCoverA
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q) (1,0)

def annularCoverB
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q) (0,1)

theorem annularCover_form_rep
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q v : Plane) :
    γ (D.handleAnnularCover q) (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v)=
      D.annularCoverA γ q*v.1+D.annularCoverB γ q*v.2 := by
  let L := euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q)
  change L v=L (1,0)*v.1+L (0,1)*v.2
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  rw [show L v=L (v.1 • (1,0)+v.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem globalSurfaceFirstPrimitive_cover
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω) (H : V → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M)
    (ℓ : ℝ) (p : Plane × V) (hp : cylinderCover p.1∈D.chart.source)
    (hN : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b p.1.1*H p.2) • D.dual (D.handleAnnularCover p.1)) :
    euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceFirstPrimitive D b Φ H Γ (ℓ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,p)=
      surfaceFirstPrimitive Φ (intervalClock (-b) b) H
        (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (ℓ,p) := by
  have hn := globalSurfaceFirstPrimitive_normal D b Φ H Γ γ (ℓ,p.2) (x := D.handleAnnularCover p.1)
    (D.chart.map_source hp)
  have hi := D.handleAnnularCover_inverse hp
  have hN' : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b (D.chart.symm (D.handleAnnularCover p.1)).1*H p.2) •
        D.dual (D.handleAnnularCover p.1) := by
    simpa only [hi,cylinderCover] using hN
  have he := hn hN'
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.handleAnnularCover p.1
  have hd (u : Plane) : D.dual (D.handleAnnularCover p.1) (A u) =
      D.clock (circleTurn p.1.2) * u.2 := D.dual_cover hp u
  have hr (u : Plane) : D.radial b (D.handleAnnularCover p.1) (A u) =
      deriv (intervalClock (-b) b) p.1.1 * u.1 := D.radial_cover b hp u
  have hg (u : Plane) : γ (D.handleAnnularCover p.1) (A u) =
      D.annularCoverA γ p.1 * u.1 + D.annularCoverB γ p.1 * u.2 :=
    D.annularCover_form_rep γ p.1 u
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ (D.handleAnnularCover_smoothAt hp)]
  change (globalSurfaceFirstPrimitive D b Φ H Γ (ℓ,p.2) (D.handleAnnularCover p.1))
    (A v.1)=_
  erw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,hi,cylinderCover,
    hd, hr, hg,
    surfaceSuspensionCoefficient,surfaceFirstPrimitive,horizontalOneForm_apply]
  ring

theorem globalSurfaceSecondPrimitive_cover {ι : Type*} [Fintype ι]
    (D : AnnularHandleData E M)
    (b : ℝ) (Φ : CompactHamiltonianIsotopy Ω)
    (K H : V → ℝ) (h : ι → V → ℝ) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ)
    (Γ : V → ManifoldOneForm E M) (γ : ManifoldOneForm E M)
    (τ : ℝ) (p : Plane × V) (hp : cylinderCover p.1∈D.chart.source)
    (hN : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b p.1.1*H p.2) • D.dual (D.handleAnnularCover p.1)) :
    euclideanPullbackOneForm
      (fun _ => productHorizontalLift (fun v => globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,v)))
      (flatProductMap (D.handleAnnularCover)) (0,p)=
      surfaceSecondPrimitive Φ (intervalClock (-b) b) K H h ρ ρ₀
        (D.annularCoverA γ) (D.annularCoverB γ) (fun q => D.clock (circleTurn q.2)) (τ,p) := by
  have hn := globalSurfaceSecondPrimitive_normal D b Φ K H h ρ ρ₀ Γ γ (τ,p.2) (x := D.handleAnnularCover p.1)
    (D.chart.map_source hp)
  have hi := D.handleAnnularCover_inverse hp
  have hN' : Γ p.2 (D.handleAnnularCover p.1)=γ (D.handleAnnularCover p.1)+
      (intervalClock (-b) b (D.chart.symm (D.handleAnnularCover p.1)).1*H p.2) •
        D.dual (D.handleAnnularCover p.1) := by
    simpa only [hi,cylinderCover] using hN
  have he := hn hN'
  let A : Plane →L[ℝ] E := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.handleAnnularCover p.1
  have hd (u : Plane) : D.dual (D.handleAnnularCover p.1) (A u) =
      D.clock (circleTurn p.1.2) * u.2 := D.dual_cover hp u
  have hr (u : Plane) : D.radial b (D.handleAnnularCover p.1) (A u) =
      deriv (intervalClock (-b) b) p.1.1 * u.1 := D.radial_cover b hp u
  have hg (u : Plane) : γ (D.handleAnnularCover p.1) (A u) =
      D.annularCoverA γ p.1 * u.1 + D.annularCoverB γ p.1 * u.2 :=
    D.annularCover_form_rep γ p.1 u
  apply ContinuousLinearMap.ext
  intro v
  rw [productHorizontalLift_pullback_apply _ (D.handleAnnularCover_smoothAt hp)]
  change (globalSurfaceSecondPrimitive D b Φ K H h ρ ρ₀ Γ (τ,p.2) (D.handleAnnularCover p.1))
    (A v.1)=_
  erw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,hi,cylinderCover,
    hd, hr, hg,
    surfaceSuspensionCoefficient,surfaceSecondPrimitive,horizontalOneForm_apply,one_mul]
  ring

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
