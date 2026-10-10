import Mathlib
import OAI.Geometry.BallPacking.Residues.AreaPolarChart

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_inverse_on {f : E → F} {D : Set E} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (hfi : InjOn f D)
    (hi : ∀ x ∈ D, (fderiv ℝ f x).IsInvertible) :
    IsOpen (f '' D) ∧ ContDiffOn ℝ ∞ (invFunOn f D) (f '' D) ∧
      (∀ x ∈ D, invFunOn f D (f x) = x) ∧
      (∀ y ∈ f '' D, f (invFunOn f D y) = y) := by
  have hlocal (x : E) (hx : x ∈ D) :
      f '' D ∈ 𝓝 (f x) ∧ ContDiffAt ℝ ∞ (invFunOn f D) (f x) := by
    have hfx : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hD.mem_nhds hx)
    obtain ⟨A,hA⟩ := hi x hx
    have hd : HasFDerivAt f (A : E →L[ℝ] F) x := by
      rw [hA]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    let e := hfx.toOpenPartialHomeomorph f hd (by simp)
    have hex : x ∈ e.source := hfx.mem_toOpenPartialHomeomorph_source hd (by simp)
    have heq : (e : E → F) = f := rfl
    let V : Set F := e '' (e.source ∩ D)
    have hV : IsOpen V := e.isOpen_image_of_subset_source (e.open_source.inter hD) inter_subset_left
    have hxV : f x ∈ V := ⟨x,⟨hex,hx⟩,rfl⟩
    have hVD : V ⊆ f '' D := by
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨z,hz.2,rfl⟩
    have hginv : invFunOn f D =ᶠ[𝓝 (f x)] e.symm := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      obtain ⟨z,hz,rfl⟩ := hy
      rw [e.left_inv hz.1]
      exact hfi.leftInvOn_invFunOn hz.2
    have hei : ContDiffAt ℝ ∞ (e.symm : F → E) (f x) :=
      hfx.to_localInverse hd (by simp)
    exact ⟨Filter.mem_of_superset (hV.mem_nhds hxV) hVD,hei.congr_of_eventuallyEq hginv⟩
  refine ⟨?_,?_,fun x hx => hfi.leftInvOn_invFunOn hx,?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).1
  · rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).2.contDiffWithinAt
  · intro y hy
    exact invFunOn_eq hy

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem clockGraph_linear_invertible (C : (Q × E) →L[ℝ] E)
    (hC : (C.comp (ContinuousLinearMap.inr ℝ Q E)).IsInvertible) :
    ((ContinuousLinearMap.fst ℝ Q E).prod C).IsInvertible := by
  let A := C.comp (ContinuousLinearMap.inr ℝ Q E)
  let B := (ContinuousLinearMap.fst ℝ Q E).prod C
  have hdecomp (p : Q × E) : C p = C (p.1,0) + A p.2 := by
    change C p = C (p.1,0) + C (0,p.2)
    rw [← map_add]
    congr 1
    ext <;> simp
  have hinj : Injective B := by
    intro p q he
    change (p.1,C p) = (q.1,C q) at he
    have ht := congrArg (fun z : Q × E => z.1) he
    have hx : C p = C q := congrArg (fun z : Q × E => z.2) he
    rw [hdecomp p,hdecomp q,ht] at hx
    have hs : p.2 = q.2 := hC.injective (add_left_cancel hx)
    exact Prod.ext ht hs
  have hsurj : Surjective B := by
    rintro ⟨t,x⟩
    refine ⟨(t,A.inverse (x-C (t,0))),?_⟩
    change (t,C (t,A.inverse (x-C (t,0)))) = (t,x)
    refine Prod.ext (by rfl) ?_
    change C (t,A.inverse (x-C (t,0))) = x
    rw [hdecomp,hC.self_apply_inverse]
    exact add_sub_cancel _ _
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj),rfl⟩

theorem parametric_inverse_on (f : Q × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (Q × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible) :
    ∃ (U : Set (Q × E)) (g : Q × E → E), IsOpen U ∧ ContDiffOn ℝ ∞ g U ∧
      U = (fun p => (p.1,f p)) '' D ∧
      (∀ p ∈ D, (p.1,f p) ∈ U ∧ g (p.1,f p) = p.2) ∧
      (∀ p ∈ U, (p.1,g p) ∈ D ∧ f (p.1,g p) = p.2) := by
  let F : Q × E → Q × E := fun p => (p.1,f p)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hFi : InjOn F D := by
    rintro ⟨t,x⟩ hp ⟨s,y⟩ hq he
    have ht : t = s := congrArg (fun z : Q × E => z.1) he
    cases ht
    have hx : f (t,x) = f (t,y) := congrArg (fun z : Q × E => z.2) he
    exact Prod.ext rfl (hinj t hp hq hx)
  have hFd (p : Q × E) : fderiv ℝ F p =
      (ContinuousLinearMap.fst ℝ Q E).prod (fderiv ℝ f p) := by
    exact (hasFDerivAt_fst.prodMk (hf.differentiable (by simp) p).hasFDerivAt).fderiv
  have hFiv (p : Q × E) (hp : p ∈ D) : (fderiv ℝ F p).IsInvertible := by
    rw [hFd]
    apply clockGraph_linear_invertible
    have hd : fderiv ℝ (fun x => f (p.1,x)) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Q E) := by
      exact ((hf.differentiable (by simp) p).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
    rw [← hd]
    exact hi p hp
  obtain ⟨hU,hg,hleft,hright⟩ := smooth_inverse_on hD hF.contDiffOn hFi hFiv
  let g : Q × E → E := fun p => (invFunOn F D p).2
  refine ⟨F '' D,g,hU,hg.snd,rfl,?_,?_⟩
  · intro p hp
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    exact congrArg Prod.snd (hleft p hp)
  · intro p hp
    have he := hright p hp
    change ((invFunOn F D p).1,f (invFunOn F D p)) = p at he
    have hfirst := congrArg (fun z : Q × E => z.1) he
    have hmem := invFunOn_mem hp
    have hid : (p.1,g p) = invFunOn F D p := Prod.ext hfirst.symm rfl
    rw [hid]
    exact ⟨hmem,congrArg (fun z : Q × E => z.2) he⟩


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem exists_compact_time_isotopy {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t x, x ∉ S → X (t,x) = 0) :
    ∃ Φ : ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,u t)) t) →
        ∀ t, Φ t (u 0) = u (Real.smoothTransition t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (L:ℝ)
  have hN0 : (0:ℝ) < N := L.coe_nonneg.trans_lt hN
  let h : ℝ → ℝ := fun t => Real.smoothTransition t / N
  have hh (t : ℝ) : ‖h t‖ * L < 1 := by
    change ‖Real.smoothTransition t / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t),div_mul_eq_mul_div]
    apply (div_lt_one hN0).mpr
    exact (mul_le_of_le_one_left L.coe_nonneg (Real.smoothTransition.le_one t)).trans_lt hN
  have hhs : ContDiff ℝ ∞ h := Real.smoothTransition.contDiff.div_const N
  let Φ : ℝ → E ≃ₜ E := fun t => timeSteps X hX hXs (hh t) 0 N
  have hsm := timeSteps_variable_smooth X hX hXs hhs (contDiff_const (c := (0:ℝ))) hh N
  refine ⟨Φ,hsm.1,hsm.2,?_,?_,?_⟩
  · ext x
    change timeSteps X hX hXs (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero X hX hXs 0 N x
  · intro t x hx
    exact timeSteps_of_stationary X hX hXs (hh t) 0 N (fun r => hs r x hx)
  · intro u hu hud t
    have he : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,he] using timeSteps_eq_solution X hX hXs (hh t) u hu hud 0 N

theorem exists_isotopy_extension
    (f g : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, (t,f (t,a)) ∈ U)
    (hinv : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g (t,f (t,a)) = a)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  let V : ℝ × E → E := fun p => fderiv ℝ f (p.1,g p) (1,0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set (ℝ × E) := (fun p : ℝ × E => (p.1,f p)) '' (Icc (0:ℝ) 1 ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨t,a⟩,⟨ht,ha⟩,rfl⟩
    exact htrack t ht a ha
  obtain ⟨χ,hχ,hχc,hχU,_,hχ1,hXs,hXc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let X : C(ℝ × E,E) := ⟨fun p => χ p • V p,hXs.continuous⟩
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (x : E) (hx : x ∉ S) : X (t,x) = 0 := by
    have hn : (t,x) ∉ tsupport χ := fun hp => hx ⟨(t,x),hp,rfl⟩
    change χ (t,x) • V (t,x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_compact_time_isotopy X hL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro t a ha
  apply hΦu (fun t => f (t,a)) (hf.continuous.comp (continuous_id.prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f (t,a)) (fderiv ℝ f (r,a) (1,0)) r :=
    (hf.differentiable (by simp) (r,a)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r a))
  convert hd using 1
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : (r,f (r,a)) ∈ C := ⟨(r,a),⟨hr',ha⟩,rfl⟩
    have hχr : χ (r,f (r,a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hχr,one_smul,hinv r hr' a ha]
  · change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hstationary r hr,hstationary r hr,smul_zero]

theorem exists_embedding_isotopy_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (ℝ × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : Icc (0:ℝ) 1 ×ˢ K ⊆ D)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_isotopy_extension f g hf U hU hg K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).1
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).2
  · exact hstationary


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeSteps_fiber_variable_smooth {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ → ℝ} (hhs : ContDiff ℝ ∞ h) (hh : ∀ t, ‖h t‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N p.2) ∧
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N).symm p.2) := by
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  let Ψ : ℝ → (P × E) ≃ₜ (P × E) := fun t => timeSteps (parameterField X)
    (parameterField_lipschitz X hX) (parameterField_smooth X hXs) (hh t) 0 N
  have hΨ : ContDiff ℝ ∞ (fun p : ℝ × (P × E) => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (P × E) => (Ψ p.1).symm p.2) :=
    timeSteps_variable_smooth (E := P × E) (Q := ℝ) (L := L)
      (parameterField X) (parameterField_lipschitz X hX)
      (parameterField_smooth X hXs) (h := h) (t := fun _ : ℝ => 0)
      hhs contDiff_const hh N
  have he (t : ℝ) (p : P × E) : Ψ t p = (p.1,Φ p.1 t p.2) :=
    timeSteps_fiber X hX hXs (hh t) 0 N p.1 p.2
  have hei (t : ℝ) (p : P × E) : (Ψ t).symm p = (p.1,(Φ p.1 t).symm p.2) := by
    apply (Ψ t).injective
    rw [(Ψ t).apply_symm_apply,he,(Φ p.1 t).apply_symm_apply]
  have hswap : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (p.1.2,(p.1.1,p.2))) :=
    contDiff_fst.snd.prodMk (contDiff_fst.fst.prodMk contDiff_snd)
  constructor
  · have hhsm := (hΨ.1.comp hswap).snd
    convert hhsm using 1
    funext p
    exact (congrArg Prod.snd (he p.1.2 (p.1.1,p.2))).symm
  · have hhsm := (hΨ.2.comp hswap).snd
    convert hhsm using 1
    funext p
    exact (congrArg Prod.snd (hei p.1.2 (p.1.1,p.2))).symm

theorem exists_parametric_time_isotopy {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t y x, x ∉ S → X (t,(y,x)) = 0) :
    ∃ Φ : P → ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,(y,u t))) t) →
        ∀ t, Φ y t (u 0) = u (Real.smoothTransition t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (L:ℝ)
  have hN0 : (0:ℝ) < N := L.coe_nonneg.trans_lt hN
  let h : ℝ → ℝ := fun t => Real.smoothTransition t / N
  have hh (t : ℝ) : ‖h t‖ * L < 1 := by
    change ‖Real.smoothTransition t / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t),div_mul_eq_mul_div]
    apply (div_lt_one hN0).mpr
    exact (mul_le_of_le_one_left L.coe_nonneg (Real.smoothTransition.le_one t)).trans_lt hN
  have hhs : ContDiff ℝ ∞ h := Real.smoothTransition.contDiff.div_const N
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  have hΦ := timeSteps_fiber_variable_smooth X hX hXs hhs hh N
  refine ⟨Φ,hΦ.1,hΦ.2,?_,?_,?_⟩
  · intro y
    ext x
    change timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) 0 N x
  · intro y t x hx
    exact timeSteps_of_stationary (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh t) 0 N (fun r => hs r y x hx)
  · intro y u hu hud t
    have heh : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,heh] using timeSteps_eq_solution (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) u hu hud 0 N

theorem exists_parametric_isotopy_extension
    (f g : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set ((P × ℝ) × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, ((y,t),f ((y,t),a)) ∈ U)
    (hinv : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g ((y,t),f ((y,t),a)) = a)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  let V : (P × ℝ) × E → E := fun p => fderiv ℝ f (p.1,g p) ((0,1),0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set ((P × ℝ) × E) := (fun p : (P × ℝ) × E => (p.1,f p)) ''
    ((Y ×ˢ Icc (0:ℝ) 1) ×ˢ K)
  have hC : IsCompact C := ((hY.prod isCompact_Icc).prod hK).image
    (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨⟨y,t⟩,a⟩,⟨⟨hy,ht⟩,ha⟩,rfl⟩
    exact htrack y hy t ht a ha
  obtain ⟨χ,_,hχc,hχU,_,hχ1,hVs,hVc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let σ : ℝ × (P × E) → (P × ℝ) × E := fun p => ((p.2.1,p.1),p.2.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_snd.fst.prodMk contDiff_fst).prodMk contDiff_snd.snd
  let X : C(ℝ × (P × E),E) := ⟨fun p => χ (σ p) • V (σ p),(hVs.comp hσ).continuous⟩
  have hXs : ContDiff ℝ ∞ X := hVs.comp hσ
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (y : P) (x : E) (hx : x ∉ S) : X (t,(y,x)) = 0 := by
    have hn : ((y,t),x) ∉ tsupport χ := fun hp => hx ⟨((y,t),x),hp,rfl⟩
    change χ ((y,t),x) • V ((y,t),x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hVs (by simp)
  have hσL : LipschitzWith 1 σ := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one,one_mul,σ,Prod.dist_eq]
    exact le_of_eq (by ac_rfl)
  have hXL : LipschitzWith L X := by
    change LipschitzWith L ((fun p => χ p • V p) ∘ σ)
    simpa only [mul_one] using hL.comp hσL
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_parametric_time_isotopy X hXL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy t a ha
  apply hΦu y (fun t => f ((y,t),a))
    (hf.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f ((y,t),a))
      (fderiv ℝ f ((y,r),a) ((0,1),0)) r :=
    (hf.differentiable (by simp) ((y,r),a)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_const r y).prodMk (hasDerivAt_id r)).prodMk (hasDerivAt_const r a))
  convert hd using 1
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : ((y,r),f ((y,r),a)) ∈ C := ⟨((y,r),a),⟨⟨hy,hr'⟩,ha⟩,rfl⟩
    have hχr : χ ((y,r),f ((y,r),a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hχr,one_smul,hinv y hy r hr' a ha]
  · change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hstationary y r hr,hstationary y r hr,smul_zero]

theorem exists_parametric_embedding_isotopy_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set ((P × ℝ) × E)) (hD : IsOpen D)
    (hinj : ∀ q, InjOn (fun x => f (q,x)) {x | (q,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : (Y ×ˢ Icc (0:ℝ) 1) ×ˢ K ⊆ D)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_parametric_isotopy_extension f g hf U hU hg Y hY K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).1
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).2
  · exact hstationary


end

open scoped ContDiff Topology NNReal
open Set Function

theorem smoothTransition_deriv_eq_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have hm : IsLocalMin Real.smoothTransition x := by
      apply IsMinOn.isLocalMin (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.zero_of_nonpos hx]
      exact Real.smoothTransition.nonneg y
    exact hm.deriv_eq_zero
  · have hm : IsLocalMax Real.smoothTransition x := by
      apply IsMaxOn.isLocalMax (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.one_of_one_le hx]
      exact Real.smoothTransition.le_one y
    exact hm.deriv_eq_zero

theorem scalar_path_sublevel_iff {v v' : ℝ → ℝ} {c ε a b : ℝ} (hε : 0 < ε)
    (hv : ContinuousOn v (Icc a b))
    (hvd : ∀ s ∈ Ico a b, HasDerivWithinAt v (v' s) (Ici s) s)
    (hzero : ∀ s ∈ Ico a b, |v s-c| < ε → v' s = 0)
    {s : ℝ} (hs : s ∈ Icc a b) : v s ≤ c ↔ v a ≤ c := by
  let f : ℝ → ℝ := fun s => Real.smoothTransition ((v s-c)/ε)
  have hf : ContinuousOn f (Icc a b) :=
    Real.smoothTransition.continuous.comp_continuousOn ((hv.sub continuousOn_const).div_const ε)
  have hβ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hfd (r : ℝ) (hr : r ∈ Ico a b) :
      HasDerivWithinAt f 0 (Ici r) r := by
    have hd := (hβ.differentiable (by simp)
      ((v r-c)/ε)).hasDerivAt.comp_hasDerivWithinAt r
        (((hvd r hr).sub_const c).div_const ε)
    change HasDerivWithinAt f
      (deriv Real.smoothTransition ((v r-c)/ε) * (v' r/ε)) (Ici r) r at hd
    by_cases hc : |v r-c| < ε
    · simpa only [hzero r hr hc,zero_div,mul_zero] using hd
    · have ho : (v r-c)/ε ≤ 0 ∨ 1 ≤ (v r-c)/ε := by
        rcases le_total (v r) c with h | h
        · exact Or.inl (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hε.le)
        · right
          rw [abs_of_nonneg (sub_nonneg.mpr h)] at hc
          exact (le_div_iff₀ hε).mpr (by linarith)
      simpa only [smoothTransition_deriv_eq_zero ho,zero_mul] using hd
  have he := constant_of_has_deriv_right_zero hf hfd s hs
  have h1 : f s = 0 ↔ v s ≤ c := by
    simp only [f,Real.smoothTransition.zero_iff_nonpos,div_le_iff₀ hε,zero_mul,sub_nonpos]
  have h0 : f a = 0 ↔ v a ≤ c := by
    simp only [f,Real.smoothTransition.zero_iff_nonpos,div_le_iff₀ hε,zero_mul,sub_nonpos]
  rw [← h1,← h0,he]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem clockPath_sublevel_iff {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) {μ : E → ℝ} (hμ : Differentiable ℝ μ)
    {c ε : ℝ} (hε : 0 < ε)
    (htan : ∀ t x, |μ x-c| < ε → fderiv ℝ μ x (X (t,x)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x : E) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    μ ((extendPath (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x)) s).2) ≤ c ↔ μ x ≤ c := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let v : ℝ → E := fun s => (extendPath u s).2
  have hc : ContinuousOn (μ ∘ v) (Icc (0:ℝ) 1) :=
    (hμ.continuous.comp (extendPath u).continuous.snd).continuousOn
  have hd (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt (μ ∘ v)
        (h * fderiv ℝ μ (v s) (X ((extendPath u s).1,v s))) (Ici s) s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have hd0 : HasDerivWithinAt v (h • X (extendPath u s)) (Icc (0:ℝ) 1) s :=
      (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivWithinAt s
        (fixedStep_derivative Y hY hh (t,x) hs')
    have hd1 := hd0.mono_of_mem_nhdsWithin (s := Ici s) (by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2),
        (self_mem_nhdsWithin : Ici s ∈ 𝓝[Ici s] s)] with q hq hsq
      exact ⟨hs.1.trans hsq,hq.le⟩)
    have hd2 := (hμ (v s)).hasFDerivAt.comp_hasDerivWithinAt s hd1
    simpa only [map_smul,smul_eq_mul,Prod.mk.eta] using hd2
  have hv0 : v 0 = x := by
    change (extendPath u 0).2 = x
    rw [show extendPath u 0 = u ⟨0,by simp⟩ from extendPath_coe u ⟨0,by simp⟩]
    change (fixedStep Y hY h (t,x) ⟨0,by simp⟩).2 = x
    rw [fixedStep_initial Y hY hh]
  have he := scalar_path_sublevel_iff hε hc hd (by
      intro r _ hr
      rw [htan _ _ hr,mul_zero]) hs
  simpa only [Function.comp_apply,hv0] using he

theorem timeStep_sublevel_iff {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) {μ : E → ℝ} (hμ : Differentiable ℝ μ)
    {c ε : ℝ} (hε : 0 < ε)
    (htan : ∀ t x, |μ x-c| < ε → fderiv ℝ μ x (X (t,x)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x : E) :
    μ (timeStep X hX h t x) ≤ c ↔ μ x ≤ c := by
  have he := clockPath_sublevel_iff X hX hμ hε htan hh t x (s := 1) (by simp)
  rw [show extendPath (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x)) 1 =
    fixedStep (clockField X) (clockField_lipschitz X hX) h (t,x) ⟨1,by simp⟩ from
      extendPath_coe _ ⟨1,by simp⟩] at he
  exact he

theorem timeStep_strict_sublevel_iff {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) {μ : E → ℝ} (hμ : Differentiable ℝ μ)
    {c ε : ℝ} (hε : 0 < ε)
    (htan : ∀ t x, |μ x-c| < ε → fderiv ℝ μ x (X (t,x)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x : E) :
    μ (timeStep X hX h t x) < c ↔ μ x < c := by
  have he := timeStep_sublevel_iff X hX hμ.neg (c := -c) hε (by
    intro t x hx
    have hx' : |μ x-c| < ε := by
      simpa only [Pi.neg_apply,neg_sub_neg,abs_sub_comm] using hx
    simp only [fderiv_neg,neg_apply,htan t x hx',neg_zero]) hh t x
  simpa only [Pi.neg_apply,neg_le_neg_iff,not_le] using not_congr he

variable [FiniteDimensional ℝ E]

theorem timeSteps_sublevel_iff {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {μ : E → ℝ} (hμ : Differentiable ℝ μ) {c ε : ℝ} (hε : 0 < ε)
    (htan : ∀ t x, |μ x-c| < ε → fderiv ℝ μ x (X (t,x)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x : E) :
    μ (timeSteps X hX hXs hh t N x) ≤ c ↔ μ x ≤ c := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change μ (timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N x)) ≤ c ↔ _
    rw [timeStep_sublevel_iff X hX hμ hε htan hh,ih]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
