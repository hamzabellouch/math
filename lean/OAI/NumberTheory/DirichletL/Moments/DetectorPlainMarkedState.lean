import OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import OAI.NumberTheory.DirichletL.Energy.Bands
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_slot_coefficient (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0<U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=>conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem retained_eq_initial_energy (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1≤U)(hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=initialState η Q Φ bΦ U δ hU hδ hs hp hη
    retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*
          annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=>idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=>idealCoeff η.inverse I*
        annularWeight (fun x=>conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,initialState,NaturalState.mask,
    detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U):
    length U (U^F.m)=F.m := by
  have hm:0≤F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1<U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0≤δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s)≤1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val)≤1+δ := by
  rw [plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem selected_widths (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(hselected:selected⊆F.slots):
    (∀s:selected,0<F.widths s.val) ∧ (∀s:selected,F.widths s.val≤F.mesh) :=
  ⟨fun s=>F.widths_pos s.val (hselected s.property),
    fun s=>F.widths_mesh s.val (hselected s.property)⟩

theorem source_profile_uniform (S:ProbeFinalAssembly.SourceData D)(Hsemin:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤height→
      (∀s,(ζ s).re=17/50)→(∀s,|(ζ s).im|≤height)→∀s,
      Hsemin.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz S (ζ s))≤
        C*(1+height)^J :=
  slotSchwartz_height_uniform S Hsemin

theorem source_relative_fixed_gates (S:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal S) η≠0 ∧
    internalQ (sourceFixedIdeal S) η≤S.modulus ∧
    internalQ (sourceFixedIdeal S) η≤η.inverse.modulus ∧
    internalQ (sourceFixedIdeal S) η≤Ideal.span {(72:O)} :=
  source_fixed_gates S η

theorem fixed_window_data (S:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=>conj (S.W x))⊆Set.Icc (1:ℝ) 2 ∧
    ContDiff ℝ ∞ (fun x=>conj (S.W x)) ∧ ∀x,‖conj (S.W x)‖≤1 := by
  refine ⟨conjugate_source_support S,
    Complex.conjCLE.contDiff.comp (S.W.smooth ⊤),?_⟩
  intro x
  rw [RCLike.norm_conj,S.complex_eq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (S.bounded x).1]
  exact (S.bounded x).2

theorem source_batch_marked_initial (S:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*(3/4+2*Δ)*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*(3/4+2*Δ)*(∑s:selected,F.widths s.val)≤state.width ∧
        (∀s:selected,0<F.widths s.val ∧ F.widths s.val≤F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0<d:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.CenteredMomentDetectorPlainMarkedState

end

end OAI
