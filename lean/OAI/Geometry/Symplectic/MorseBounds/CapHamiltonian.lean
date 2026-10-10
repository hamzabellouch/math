import OAI.Geometry.Symplectic.MorseBounds.CapGluing

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapHamiltonian
open MorseArnold.CapGluing
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
variable {ι M N E F : Type*} [Fintype ι] [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ChartedSpace E M] [ChartedSpace F N] [IsManifold 𝓘(ℝ,E) ∞ M]
  [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space M]
local notation "I" => 𝓘(ℝ,E)
local notation "J" => 𝓘(ℝ,F)
local instance capHamiltonianPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable

def insertVector (e : ι → OpenPartialHomeomorph M N)
    (V : ℝ → (y : N) → TangentSpace J y) (t : ℝ) (x : M) : TangentSpace I x :=
  show E from if h : ∃ i, x ∈ (e i).source then
    let i := Classical.choose h
    mfderiv J I (e i).symm (e i x) (V t (e i x))
  else 0

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space M] in
lemma insertVector_in_source
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (V : ℝ → (y : N) → TangentSpace J y) (t : ℝ) (i : ι) (x : M)
    (hx : x ∈ (e i).source) :
    insertVector (E := E) e V t x = mfderiv J I (e i).symm (e i x) (V t (e i x)) := by
  have hex : ∃ j, x ∈ (e j).source := ⟨i,hx⟩
  have hj : Classical.choose hex = i := source_index_unique e hdis (Classical.choose_spec hex) hx
  change (if h : ∃ j, x ∈ (e j).source then
    (mfderiv J I (e (Classical.choose h)).symm (e (Classical.choose h) x)
      (V t (e (Classical.choose h) x)) : E) else 0) = _
  erw [dite_eq_left hex]
  erw [hj]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space M] in
lemma insertVector_outside
    (e : ι → OpenPartialHomeomorph M N)
    (V : ℝ → (y : N) → TangentSpace J y) (t : ℝ) (x : M)
    (hx : ∀ i, x ∉ (e i).source) : insertVector (E := E) e V t x = 0 := by
  change (if h : ∃ j, x ∈ (e j).source then
    (mfderiv J I (e (Classical.choose h)).symm (e (Classical.choose h) x)
      (V t (e (Classical.choose h) x)) : E) else 0) = _
  exact dite_eq_right (not_exists.mpr hx)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space M] in
lemma chart_inverse_derivative (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source)
    (hei : ContMDiffOn J I ∞ e.symm e.target)
    (x : M) (hx : x ∈ e.source) (v : TangentSpace J (e x)) :
    mfderiv I J e x (mfderiv J I e.symm (e x) v) = v := by
  have he' := ((he x hx).contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hi' := ((hei (e x) (e.map_source hx)).contMDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).mdifferentiableAt (by simp)
  have he'' : MDifferentiableAt I J e (e.symm (e x)) := by rw [e.left_inv hx]; exact he'
  have hh := he''.hasMFDerivAt.comp (e x) hi'.hasMFDerivAt
  have hloc : (id : N → N) =ᶠ[𝓝 (e x)] e ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact (e.right_inv hy).symm
  have hd := (hh.congr_of_eventuallyEq hloc).mfderiv
  rw [mfderiv_id] at hd
  have hdv := congrArg (fun L => L v) hd
  change (v : F) = (mfderiv I J e (e.symm (e x)) : E →L[ℝ] F)
    ((mfderiv J I e.symm (e x) : F →L[ℝ] E) v) at hdv
  have heq := congrArg (β := E →L[ℝ] F) (fun y : M => (show E →L[ℝ] F from mfderiv I J e y)) (e.left_inv hx)
  have heqv := congrArg (fun L : E →L[ℝ] F => L
    (show E from mfderiv J I e.symm (e x) v)) heq
  exact heqv.symm.trans hdv.symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space M] in
lemma generator_derivative_inside
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (K : ℝ × N → ℝ) (hK : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ K)
    (t : ℝ) (i : ι) (x : M) (hx : x ∈ (e i).source) :
    mvfderiv I (fun z => generator e K (t,z)) x =
      (mvfderiv J (fun z => K (t,z)) (e i x)).comp (mfderiv I J (e i) x) := by
  have he' := (((he i) x hx).contMDiffAt ((e i).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hKs : ContMDiff J 𝓘(ℝ) ∞ (fun z => K (t,z)) :=
    hK.comp (contMDiff_const.prodMk contMDiff_id)
  have hK' := hKs.mdifferentiable (by simp) (e i x)
  have hh := hK'.hasMFDerivAt.comp x he'.hasMFDerivAt
  have heq : (fun z => generator e K (t,z)) =ᶠ[𝓝 x] (fun z => K (t,e i z)) := by
    filter_upwards [(e i).open_source.mem_nhds hx] with z hz
    exact generator_in_source e hdis K t i z hz
  exact (hh.congr_of_eventuallyEq heq).mfderiv

lemma zeroExtend_zero_near_outside (e : OpenPartialHomeomorph M N)
    (C : Set N) (hC : IsCompact C) (hsub : C ⊆ e.target)
    (K : ℝ × N → ℝ) (hzero : ∀ t y, y ∉ C → K (t,y) = 0)
    (t : ℝ) (x : M) (hx : x ∉ e.source) :
    (fun z => zeroExtend e K (t,z)) =ᶠ[𝓝 x] 0 := by
  have hc : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hsub)).isClosed
  have hn : x ∉ e.symm '' C := by
    rintro ⟨y,hy,hxy⟩
    exact hx (hxy ▸ e.map_target (hsub hy))
  filter_upwards [hc.isOpen_compl.mem_nhds hn] with z hz
  by_cases hs : z ∈ e.source
  · exact (ite_eq_left hs).trans (hzero t (e z) (coord_not_mem e C hs hz))
  · exact ite_eq_right hs

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma generator_derivative_outside
    (e : ι → OpenPartialHomeomorph M N)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (K : ℝ × N → ℝ) (hzero : ∀ t y, y ∉ C → K (t,y) = 0)
    (t : ℝ) (x : M) (hx : ∀ i, x ∉ (e i).source) :
    mvfderiv I (fun z => generator e K (t,z)) x = 0 := by
  have hloc : (fun z => generator e K (t,z)) =ᶠ[𝓝 x] 0 := by
    have hz : ∀ᶠ z in 𝓝 x, ∀ i, zeroExtend (e i) K (t,z) = 0 := by
      exact Filter.eventually_all.mpr (fun i => zeroExtend_zero_near_outside
        (e i) C hC (hsub i) K hzero t x (hx i))
    filter_upwards [hz] with z hz
    simp [generator,hz]
  have hh := (hasMFDerivAt_const («I» := I) (I' := 𝓘(ℝ)) (0 : ℝ) x).congr_of_eventuallyEq hloc
  exact hh.mfderiv

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
lemma insertVector_hamiltonian
    (wM : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (wN : (y : N) → TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (hw : ∀ i x, x ∈ (e i).source → ∀ u v,
      wN (e i x) (mfderiv I J (e i) x u) (mfderiv I J (e i) x v) = wM x u v)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (K : ℝ × N → ℝ) (V : ℝ → (y : N) → TangentSpace J y)
    (hK : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ K)
    (hzero : ∀ t y, y ∉ C → K (t,y) = 0)
    (hV : ∀ t y, wN y (V t y) = mvfderiv J (fun z => K (t,z)) y)
    (t : ℝ) (x : M) :
    wM x (insertVector (E := E) e V t x) = mvfderiv I (fun z => generator e K (t,z)) x := by
  by_cases hs : ∃ i, x ∈ (e i).source
  · obtain ⟨i,hi⟩ := hs
    rw [insertVector_in_source e hdis V t i x hi,
      generator_derivative_inside e hdis he K hK t i x hi]
    ext v
    erw [← hw i x hi, chart_inverse_derivative (e i) (he i) (hei i) x hi, hV]
    rfl
  · rw [insertVector_outside e V t x (not_exists.mp hs),map_zero,
      generator_derivative_outside e C hC hsub K hzero t x (not_exists.mp hs)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space M] in
lemma insert_ode
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (d : ℝ × N → N) (V : ℝ → (y : N) → TangentSpace J y)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target)
    (hODE : ∀ t y, HasMFDerivAt 𝓘(ℝ) J (fun r => d (r,y)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (d (t,y)))))
    (t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun r => insert e d (r,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (insertVector (E := E) e V t (insert e d (t,x)))) := by
  by_cases hs : ∃ i, x ∈ (e i).source
  · obtain ⟨i,hi⟩ := hs
    have hy : d (t,e i x) ∈ (e i).target := hmap t i ((e i).map_source hi)
    have hdf := (((hei i) _ hy).contMDiffAt ((e i).open_target.mem_nhds hy)).mdifferentiableAt (by simp)
    have himg : insert e d (t,x) ∈ (e i).source := by
      rw [insert_in_source e hdis d t i x hi]
      exact (e i).map_target hy
    have hv : insertVector (E := E) e V t (insert e d (t,x)) =
        mfderiv J I (e i).symm (d (t,e i x)) (V t (d (t,e i x))) := by
      have hh : e i (insert e d (t,x)) = d (t,e i x) := by
        rw [insert_in_source e hdis d t i x hi, (e i).right_inv hy]
      exact (insertVector_in_source e hdis V t i _ himg).trans
        (congrArg (fun y => (mfderiv J I (e i).symm y (V t y) : E)) hh)
    have hc := hdf.hasMFDerivAt.comp t (hODE t (e i x))
    have heq : (fun r => insert e d (r,x)) =ᶠ[𝓝 t]
        ((e i).symm ∘ fun r => d (r,e i x)) :=
      Filter.Eventually.of_forall (fun r => insert_in_source e hdis d r i x hi)
    apply (hc.congr_of_eventuallyEq heq).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv J I (e i).symm (d (t,e i x)) (a • V t (d (t,e i x))) =
      a • insertVector (E := E) e V t (insert e d (t,x))
    rw [map_smul,hv]
    rfl
  · have hn := not_exists.mp hs
    have heq : (fun r => insert e d (r,x)) =ᶠ[𝓝 t] (fun _ => x) :=
      Filter.Eventually.of_forall (fun r => insert_outside e d r x hn)
    have hc := (hasMFDerivAt_const («I» := 𝓘(ℝ)) (I' := I) x t).congr_of_eventuallyEq heq
    apply hc.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change (0 : E) = a • insertVector (E := E) e V t (insert e d (t,x))
    rw [insert_outside e d t x hn,insertVector_outside e V t x hn,smul_zero]
    rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem insert_hamiltonian
    (wM : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (wN : (y : N) → TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (hw : ∀ i x, x ∈ (e i).source → ∀ u v,
      wN (e i x) (mfderiv I J (e i) x u) (mfderiv I J (e i) x v) = wM x u v)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (d : ℝ × N → N) (K : ℝ × N → ℝ)
    (V : ℝ → (y : N) → TangentSpace J y)
    (hd : ContMDiff (𝓘(ℝ).prod J) J ∞ d)
    (hK : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ K)
    (hid : ∀ t y, y ∉ C → d (t,y) = y)
    (hzero : ∀ t y, y ∉ C → K (t,y) = 0)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target)
    (hV : ∀ t y, wN y (V t y) = mvfderiv J (fun z => K (t,z)) y)
    (hODE : ∀ t y, HasMFDerivAt 𝓘(ℝ) J (fun r => d (r,y)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (d (t,y))))) :
    ∃ W : ℝ → (x : M) → TangentSpace I x,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (insert e d) ∧
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (generator e K) ∧
      (∀ t x, wM x (W t x) = mvfderiv I (fun z => generator e K (t,z)) x) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun r => insert e d (r,x)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (W t (insert e d (t,x))))) := by
  refine ⟨insertVector (E := E) e V,
    insert_smooth e hdis he hei C hC hsub d hd hid hmap,
    generator_smooth e he C hC hsub K hK hzero,
    insertVector_hamiltonian wM wN e hdis he hei hw C hC hsub K V hK hzero hV,
    insert_ode e hdis hei d V hmap hODE⟩
end
end MorseArnold.CapHamiltonian

end

end OAI
