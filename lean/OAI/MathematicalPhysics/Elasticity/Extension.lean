import Mathlib

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
attribute [local instance] Classical.propDecidable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_piecewise (s : Set E) (f g : E → F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hv : ∀ x ∈ frontier s, f x=g x)
    (hd : ∀ x ∈ frontier s, fderiv ℝ f x=fderiv ℝ g x) (x : E) :
    HasFDerivAt (s.piecewise f g) (s.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
  classical
  by_cases hb : x ∈ frontier s
  · have hvf : s.piecewise f g x=f x := by
      by_cases hx : x∈s
      · simp [hx]
      · simp [hx,hv x hb]
    have hvg : s.piecewise f g x=g x := hvf.trans (hv x hb)
    have hd' : s.piecewise (fderiv ℝ f) (fderiv ℝ g) x=fderiv ℝ f x := by
      by_cases hx : x∈s
      · simp [hx]
      · simp [hx,hd x hb]
    rw [hd']
    have h1 : HasFDerivWithinAt (s.piecewise f g) (fderiv ℝ f x) s x :=
      (hf x).hasFDerivAt.hasFDerivWithinAt.congr (by intro y hy; simp [hy]) hvf
    have h2 : HasFDerivWithinAt (s.piecewise f g) (fderiv ℝ f x) sᶜ x := by
      rw [hd x hb]
      exact (hg x).hasFDerivAt.hasFDerivWithinAt.congr (by intro y hy; exact piecewise_eq_of_notMem s f g hy) hvg
    simpa only [union_compl_self,hasFDerivWithinAt_univ] using h1.union h2
  · by_cases hx : x∈s
    · simp only [piecewise_eq_of_mem s _ _ hx]
      apply (hf x).hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [mem_interior_iff_mem_nhds.mp ((mem_interior_iff_notMem_frontier hx).mpr hb)] with y hy
      simp [hy]
    · simp only [piecewise_eq_of_notMem s _ _ hx]
      apply (hg x).hasFDerivAt.congr_of_eventuallyEq
      have hi : x∈interior sᶜ := (mem_interior_iff_notMem_frontier hx).mpr (by simpa using hb)
      filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
      exact piecewise_eq_of_notMem s f g hy

/-- Matching all actual Fréchet jets gives smooth gluing across an arbitrary interface. -/
theorem smooth_piecewise_all_jets (s : Set E) (f g : E → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hj : ∀ n : ℕ, ∀ x∈frontier s, iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x) :
    ContDiff ℝ (⊤ : ℕ∞) (s.piecewise f g) := by
  classical
  have main : ∀ n : ℕ, ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f g : E → F), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ m : ℕ, ∀ x∈frontier s, iteratedFDeriv ℝ m f x=iteratedFDeriv ℝ m g x) →
      ContDiff ℝ n (s.piecewise f g) := by
    intro n
    induction n with
    | zero =>
      intro F _ _ f g hf hg hj
      change ContDiff ℝ 0 _
      rw [contDiff_zero]
      apply Continuous.piecewise _ hf.continuous hg.continuous
      intro x hx
      have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hj 0 x hx)
      simpa using hh
    | succ n ih =>
      intro F _ _ f g hf hg hj
      have hd : ∀ m : ℕ, ∀ x∈frontier s,
          iteratedFDeriv ℝ m (fderiv ℝ f) x=iteratedFDeriv ℝ m (fderiv ℝ g) x := by
        intro m x hx
        have hh := hj (m+1) x hx
        simp only [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply] at hh
        exact (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.injective hh
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨s.piecewise (fderiv ℝ f) (fderiv ℝ g),
        ih _ _ _ (hf.fderiv_right (by simp)) (hg.fderiv_right (by simp)) hd, ?_⟩
      intro x
      apply hasFDerivAt_piecewise s f g (hf.differentiable (by simp)) (hg.differentiable (by simp))
      · intro y hy
        have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hj 0 y hy)
        simpa using hh
      · intro y hy
        have hh := congrArg (fun L => L (fun i : Fin 0 => ![] i)) (hd 0 y hy)
        simpa using hh
  exact contDiff_infty.mpr (fun n => main n F f g hf hg hj)
end ElasticityBoundary

end
end
section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

omit [FiniteDimensional ℝ E] in
lemma contDiff_cutoff_mul {U : Set E} (hU : IsOpen U) (f χ : E → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ⊆U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x*f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈U
  · exact hχ.contDiffAt.mul ((hf x hx).contDiffAt (hU.mem_nhds hx))
  · have hn : x∉tsupport χ := fun hh => hx (hs hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

/-- A genuine global smooth extension, equal on a neighborhood of the compact set. -/
theorem smooth_global_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (f : E → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ F : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ F =ᶠ[𝓝ˢ K] f := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => χ x*f x,contDiff_cutoff_mul hU f χ hf hχ hs,?_,?_⟩
  · exact hc.mul_right
  · filter_upwards [h1] with x hx
    simp [hx]

/-- Convex interpolation preserves both physical positivity inequalities. -/
theorem admissible_global_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (lam mu : E → ℝ)
    (hl : ContDiffOn ℝ (⊤ : ℕ∞) lam U) (hm : ContDiffOn ℝ (⊤ : ℕ∞) mu U)
    (hp : ∀ x∈K, 0 < mu x ∧ 0<3*lam x+2*mu x) :
    ∃ L M : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) L ∧ ContDiff ℝ (⊤ : ℕ∞) M ∧
      L =ᶠ[𝓝ˢ K] lam ∧ M =ᶠ[𝓝ˢ K] mu ∧
      (∀ x,0 < M x ∧ 0<3*L x+2*M x) ∧
      HasCompactSupport L ∧ HasCompactSupport (fun x => M x-1) := by
  obtain ⟨f,hf,_,hfl⟩ := smooth_global_extension hK hU hKU lam hl
  obtain ⟨g,hg,_,hgm⟩ := smooth_global_extension hK hU hKU mu hm
  let V := {x | 0<g x} ∩ {x | 0<3*f x+2*g x}
  have hV : IsOpen V := (isOpen_lt continuous_const hg.continuous).inter
    (isOpen_lt continuous_const ((continuous_const.mul hf.continuous).add (continuous_const.mul hg.continuous)))
  have hKV : K⊆V := by
    intro x hx
    change 0<g x ∧ 0<3*f x+2*g x
    rw [hfl.self_of_nhdsSet hx,hgm.self_of_nhdsSet hx]
    exact hp x hx
  obtain ⟨χ,hχ,hc,hs,h1,hb⟩ := compact_smooth_cutoff hK hV hKV
  let L := fun x => χ x*f x
  let M := fun x => χ x*g x+(1-χ x)
  refine ⟨L,M,hχ.mul hf,(hχ.mul hg).add (contDiff_const.sub hχ),?_,?_,?_,?_,?_⟩
  · filter_upwards [h1,hfl] with x hx hy
    simp [L,hx,hy]
  · filter_upwards [h1,hgm] with x hx hy
    simp [M,hx,hy]
  · intro x
    by_cases hx : χ x=0
    · simp [L,M,hx]
    · have hv := hs (subset_tsupport χ (show χ x≠0 from hx))
      have hpos : 0<χ x := lt_of_le_of_ne (hb x).1 (Ne.symm hx)
      have hle := (hb x).2
      have hgpos := hv.1
      have hpair := hv.2
      change 0<χ x*g x+(1-χ x) ∧ 0<3*(χ x*f x)+2*(χ x*g x+(1-χ x))
      constructor
      · nlinarith [mul_pos hpos hgpos]
      · nlinarith [mul_pos hpos hpair]
  · exact hc.mul_right
  · have he : (fun x => M x-1)=(fun x => χ x*(g x-1)) := by funext x; dsimp [M]; ring
    rw [he]
    exact hc.mul_right
end ElasticityBoundary

end
end

end OAI
