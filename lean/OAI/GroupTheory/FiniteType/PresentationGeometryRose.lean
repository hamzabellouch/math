import Mathlib
import OAI.GroupTheory.FiniteType.PresentationVanKampenRectanglePaths

namespace OAI

noncomputable section
namespace PresentationGeometry.Rose
section
open Set DiscreteCoverCharts
variable {k : ℕ}
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

noncomputable def monodromyRepresentation (g : Fin k → Q) :
    FundamentalGroup (Space k) (basepoint k) →* Equiv.Perm Q :=
  ((fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)).symm.permCongrHom.toMonoidHom).comp
      ((covering (coveringCore g)).monodromyPerm (basepoint k))

@[simp] theorem monodromyRepresentation_generator (g : Fin k → Q) (i : Fin k) (q : Q) :
    monodromyRepresentation g (freeToFundamental k (FreeGroup.of i)) q = g i * q := by
  let e := fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)
  have hg : freeToFundamental k (FreeGroup.of i) =
      (Path.Homotopic.Quotient.mk (generatorLoop i) : FundamentalGroup (Space k) (basepoint k)) := by
    exact FreeGroup.lift_apply_of (β := FundamentalGroup (Space k) (basepoint k))
      (f := fun i : Fin k =>
      (Path.Homotopic.Quotient.mk (generatorLoop i) : FundamentalGroup (Space k) (basepoint k)))
  rw [hg]
  change e.symm ((covering (coveringCore g)).monodromy
    (Path.Homotopic.Quotient.mk (generatorLoop i)) (e q)) = _
  have h : (covering (coveringCore g)).monodromy
      (Path.Homotopic.Quotient.mk (generatorLoop i)) (e q) = e (g i * q) :=
    monodromy_generator g i q
  rw [h, e.symm_apply_apply]

theorem monodromyRepresentation_comp (g : Fin k → Q) :
    (monodromyRepresentation g).comp (freeToFundamental k) =
      (MulAction.toPermHom Q Q).comp (FreeGroup.lift g) := by
  apply FreeGroup.ext_hom
  intro i
  ext q
  simp only [MonoidHom.comp_apply, monodromyRepresentation_generator,
    FreeGroup.lift_apply_of, MulAction.toPermHom_apply]
  rfl

theorem freeToFundamental_injective (k : ℕ) : Function.Injective (freeToFundamental k) := by
  let : TopologicalSpace (FreeGroup (Fin k)) := ⊥
  let : DiscreteTopology (FreeGroup (Fin k)) := ⟨rfl⟩
  have he := monodromyRepresentation_comp (Q := FreeGroup (Fin k)) FreeGroup.of
  have hlift : FreeGroup.lift (FreeGroup.of : Fin k → FreeGroup (Fin k)) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp
  rw [hlift] at he
  intro a b hab
  have h := congrArg (monodromyRepresentation (Q := FreeGroup (Fin k)) FreeGroup.of) hab
  have ha := DFunLike.congr_fun he a
  have hb := DFunLike.congr_fun he b
  change monodromyRepresentation FreeGroup.of (freeToFundamental k a) = _ at ha
  change monodromyRepresentation FreeGroup.of (freeToFundamental k b) = _ at hb
  rw [ha,hb] at h
  have h' := DFunLike.congr_fun h (1 : FreeGroup (Fin k))
  simpa using h'

noncomputable def freeGroupEquiv (k : ℕ) :
    FreeGroup (Fin k) ≃* FundamentalGroup (Space k) (basepoint k) :=
  MulEquiv.ofBijective (freeToFundamental k)
    ⟨freeToFundamental_injective k, freeToFundamental_surjective k⟩

end

open DiscreteCoverCharts
variable {k : ℕ}
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

theorem monodromy_word (g : Fin k → Q) (w : List (Fin k × Bool)) (q : Q) :
    (covering (coveringCore g)).monodromy
      (Path.Homotopic.Quotient.mk (wordLoop w))
      ⟨point (coveringCore g) none (basepoint k) q,rfl⟩ =
      ⟨point (coveringCore g) none (basepoint k) (FreeGroup.lift g (FreeGroup.mk w) * q),rfl⟩ := by
  let e := fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)
  apply e.symm.injective
  have h := DFunLike.congr_fun (monodromyRepresentation_comp g) (FreeGroup.mk w)
  have h' := DFunLike.congr_fun h q
  change monodromyRepresentation g (freeToFundamental k (FreeGroup.mk w)) q =
    FreeGroup.lift g (FreeGroup.mk w) * q at h'
  rw [freeToFundamental_mk] at h'
  change e.symm ((covering (coveringCore g)).monodromy
    (Path.Homotopic.Quotient.mk (wordLoop w)) (e q)) = e.symm (e _)
  rw [e.symm_apply_apply]
  exact h'

def liftedRelator (g : Fin k → Q) (w : List (Fin k × Bool))
    (hw : FreeGroup.lift g (FreeGroup.mk w) = 1) :
    Path (point (coveringCore g) none (basepoint k) 1)
      (point (coveringCore g) none (basepoint k) 1) where
  toContinuousMap := (covering (coveringCore g)).liftPath (wordLoop w)
    (point (coveringCore g) none (basepoint k) 1) (wordLoop w).source
  source' := (covering (coveringCore g)).liftPath_zero _ _ _
  target' := by
    have h := congrArg Subtype.val (monodromy_word g w 1)
    rw [hw,one_mul] at h
    exact h

@[simp] theorem liftedRelator_proj (g : Fin k → Q) (w : List (Fin k × Bool))
    (hw : FreeGroup.lift g (FreeGroup.mk w) = 1) (t : unitInterval) :
    (coveringCore g).proj (liftedRelator g w hw t) = wordLoop w t :=
  congrFun ((covering (coveringCore g)).liftPath_lifts (wordLoop w)
    (point (coveringCore g) none (basepoint k) 1) (wordLoop w).source) t

end PresentationGeometry.Rose

namespace PresentationGeometry.AttachingLoops
open scoped unitInterval

theorem onCircle_naturality {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (p : Path x x) (q : Path y y) (f : C(X,Y))
    (h : ∀ t, f (p t) = q t) (z : AddCircle (1 : ℝ)) :
    f (onCircle p z) = onCircle q z := by
  obtain ⟨t,ht,rfl⟩ := AddCircle.eq_coe_Ico z
  have hu : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
  change f (onCircle p (((⟨t,hu⟩ : I) : ℝ) : AddCircle (1 : ℝ))) =
    onCircle q (((⟨t,hu⟩ : I) : ℝ) : AddCircle (1 : ℝ))
  rw [onCircle_coe,onCircle_coe]
  exact h _

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

def boundaryCircle : C(Cells.boundary r 2, Fin r × AddCircle (1 : ℝ)) where
  toFun b := (b.1.1,boundaryParameter ⟨b.1.2.1,b.2⟩)
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    (boundaryParameter.continuous.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))

def liftedRelatorsOnCircle : C(Fin r × AddCircle (1 : ℝ), (Rose.coveringCore g).TotalSpace) where
  toFun p := onCircle (Rose.liftedRelator g (w p.1) (hw p.1)) p.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun i =>
    (onCircle (Rose.liftedRelator g (w i) (hw i))).continuous

def relatorSection : C(Cells.boundary r 2, (Rose.coveringCore g).TotalSpace) :=
  (liftedRelatorsOnCircle w g hw).comp boundaryCircle

@[simp] theorem relatorSection_proj (b : Cells.boundary r 2) :
    (Rose.coveringCore g).proj (relatorSection w g hw b) = relators w b := by
  exact onCircle_naturality (Rose.liftedRelator g (w b.1.1) (hw b.1.1))
    (Rose.wordLoop (w b.1.1)) ⟨_,(Rose.coveringCore g).continuous_proj⟩
    (Rose.liftedRelator_proj g (w b.1.1) (hw b.1.1)) _

end PresentationGeometry.AttachingLoops

namespace PresentationGeometry.PresentationComplex
section
open Set DiscreteCoverCharts
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

def coveringCore : FiberBundleCore (Option (Fin k) ⊕ Fin r) (Space w) Q :=
  CellCoverExtension.coveringCore (AttachingLoops.relators w) (Rose.basepoint k)
    (Rose.coveringCore g) (Rose.potential g) (AttachingLoops.relatorSection w g hw)
    (AttachingLoops.relatorSection_proj w g hw) (fun _ _ _ _ => rfl)

@[simp] theorem coveringCore_old_coordChange (i j : Option (Fin k)) (x : Rose.Space k) (q : Q) :
    (coveringCore w g hw).coordChange (.inl i) (.inl j) (includeRose w x) q =
      (Rose.coveringCore g).coordChange i j x q :=
  CellCoverExtension.coveringCore_old_coordChange ..

@[simp] theorem mem_coveringCore_old (i : Option (Fin k)) (x : Rose.Space k) :
    includeRose w x ∈ (coveringCore w g hw).baseSet (.inl i) ↔
      x ∈ (Rose.coveringCore g).baseSet i :=
  CellCoverExtension.mem_coveringCore_old ..

theorem basepoint_mem_coveringCore : basepoint w ∈ (coveringCore w g hw).baseSet (.inl none) :=
  (mem_coveringCore_old w g hw none (Rose.basepoint k)).mpr
    (Cells.mem_collar_old (Rose.attaching k) PUnit.unit)

theorem map_range_old_chart (i : Option (Fin k)) {a b : Rose.Space k} (p : Path a b)
    (hp : range p ⊆ (Rose.coveringCore g).baseSet i) :
    range (p.map (includeRose w).continuous) ⊆ (coveringCore w g hw).baseSet (.inl i) := by
  rintro _ ⟨t,rfl⟩
  exact (mem_coveringCore_old w g hw i (p t)).mpr (hp ⟨t,rfl⟩)

theorem monodromy_generator (i : Fin k) (q : Q) :
    (covering (coveringCore w g hw)).monodromy
      (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous))
      ⟨point (coveringCore w g hw) (.inl none) (basepoint w) q,rfl⟩ =
      ⟨point (coveringCore w g hw) (.inl none) (basepoint w) (g i * q),rfl⟩ := by
  let Z := coveringCore w g hw
  let p₁ := (Rose.edgeFirst i).map (includeRose w).continuous
  let p₂ := (Rose.edgeMiddle i).map (includeRose w).continuous
  let p₃ := (Rose.edgeLast i).map (includeRose w).continuous
  have hc₁ : range p₁ ⊆ Z.baseSet (.inl none) :=
    map_range_old_chart w g hw none _ (Rose.edgeFirst_collar i)
  have hc₂ : range p₂ ⊆ Z.baseSet (.inl (some i)) :=
    map_range_old_chart w g hw (some i) _ (Rose.edgeMiddle_interior i)
  have hc₃ : range p₃ ⊆ Z.baseSet (.inl none) :=
    map_range_old_chart w g hw none _ (Rose.edgeLast_collar i)
  have hn : point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q =
      point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q := by
    have h := point_change Z (.inl none) (.inl (some i))
      (hc₁ p₁.target_mem_range) (hc₂ p₂.source_mem_range) q
    simpa only [Z,coveringCore_old_coordChange,Rose.coveringCore,Rose.transition,
      Rose.potential_none,Rose.potential_negative,inv_one,one_mul] using h
  have hp : point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgePositive)) q =
      point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgePositive)) (g i * q) := by
    have h := point_change Z (.inl (some i)) (.inl none)
      (hc₂ p₂.target_mem_range) (hc₃ p₃.source_mem_range) q
    simpa only [Z,coveringCore_old_coordChange,Rose.coveringCore,Rose.transition,
      Rose.potential_none,Rose.potential_positive,inv_inv,one_mul] using h
  have he : Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous) =
      (Path.Homotopic.Quotient.mk p₁).trans
        ((Path.Homotopic.Quotient.mk p₂).trans (Path.Homotopic.Quotient.mk p₃)) := by
    simp only [← Path.Homotopic.Quotient.mk_trans]
    apply Quotient.sound
    change ((Rose.generatorLoop i).map (includeRose w).continuous).Homotopic (p₁.trans (p₂.trans p₃))
    have hh := (Rose.edge_parts_homotopic i).symm.map (includeRose w)
    simpa only [Path.map_trans] using hh
  erw [he,IsCoveringMap.monodromy_trans_apply,monodromy_chartPath Z (.inl none) _ hc₁]
  have hn' : (⟨point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q,rfl⟩ :
      Z.proj ⁻¹' {includeRose w (Rose.edgeMap i Rose.edgeNegative)}) =
      ⟨point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgeNegative)) q,rfl⟩ := Subtype.ext hn
  erw [hn',IsCoveringMap.monodromy_trans_apply,monodromy_chartPath Z (.inl (some i)) _ hc₂]
  have hp' : (⟨point Z (.inl (some i)) (includeRose w (Rose.edgeMap i Rose.edgePositive)) q,rfl⟩ :
      Z.proj ⁻¹' {includeRose w (Rose.edgeMap i Rose.edgePositive)}) =
      ⟨point Z (.inl none) (includeRose w (Rose.edgeMap i Rose.edgePositive)) (g i * q),rfl⟩ := Subtype.ext hp
  erw [hp',monodromy_chartPath Z (.inl none) _ hc₃]
  rfl

def monodromyRepresentation : FundamentalGroup (Space w) (basepoint w) →* Equiv.Perm Q :=
  ((fiberEquiv (coveringCore w g hw) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w g hw)).symm.permCongrHom.toMonoidHom).comp
      ((covering (coveringCore w g hw)).monodromyPerm (basepoint w))

@[simp] theorem monodromyRepresentation_generator (i : Fin k) (q : Q) :
    monodromyRepresentation w g hw (freeToFundamental w (FreeGroup.of i)) q = g i * q := by
  let e := fiberEquiv (coveringCore w g hw) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w g hw)
  have hg : Rose.freeToFundamental k (FreeGroup.of i) =
      (Path.Homotopic.Quotient.mk (Rose.generatorLoop i) :
        FundamentalGroup (Rose.Space k) (Rose.basepoint k)) := by
    exact FreeGroup.lift_apply_of (β := FundamentalGroup (Rose.Space k) (Rose.basepoint k))
      (f := fun i : Fin k => (Path.Homotopic.Quotient.mk (Rose.generatorLoop i) :
        FundamentalGroup (Rose.Space k) (Rose.basepoint k)))
  change monodromyRepresentation w g hw
    (FundamentalGroup.map (includeRose w) (Rose.basepoint k) (Rose.freeToFundamental k (FreeGroup.of i))) q = _
  rw [hg]
  change e.symm ((covering (coveringCore w g hw)).monodromy
    (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous)) (e q)) = _
  have h : (covering (coveringCore w g hw)).monodromy
      (Path.Homotopic.Quotient.mk ((Rose.generatorLoop i).map (includeRose w).continuous)) (e q) = e (g i * q) :=
    monodromy_generator w g hw i q
  erw [h,e.symm_apply_apply]

theorem monodromyRepresentation_comp :
    (monodromyRepresentation w g hw).comp (freeToFundamental w) =
      (MulAction.toPermHom Q Q).comp (FreeGroup.lift g) := by
  apply FreeGroup.ext_hom
  intro i
  ext q
  simp only [MonoidHom.comp_apply,monodromyRepresentation_generator,
    FreeGroup.lift_apply_of,MulAction.toPermHom_apply]
  rfl

end

section
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

theorem presentedToFundamental_injective : Function.Injective (presentedToFundamental w) := by
  let Q := PresentedGroup (relatorSet w)
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let g : Fin k → Q := PresentedGroup.of
  have hg : FreeGroup.lift g = PresentedGroup.mk (relatorSet w) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of]
    rfl
  have hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1 := by
    intro i
    rw [hg]
    exact PresentedGroup.one_of_mem ⟨i,rfl⟩
  let m := monodromyRepresentation w g hw
  have hm := monodromyRepresentation_comp w g hw
  rw [hg] at hm
  intro a b hab
  obtain ⟨a,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) a
  obtain ⟨b,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) b
  rw [presentedToFundamental_mk,presentedToFundamental_mk] at hab
  have h := congrArg m hab
  have ha := DFunLike.congr_fun hm a
  have hb := DFunLike.congr_fun hm b
  change m (freeToFundamental w a) = _ at ha
  change m (freeToFundamental w b) = _ at hb
  rw [ha,hb] at h
  have h' := DFunLike.congr_fun h (1 : Q)
  simpa using h'

def presentationEquiv : PresentedGroup (relatorSet w) ≃*
    FundamentalGroup (Space w) (basepoint w) :=
  MulEquiv.ofBijective (presentedToFundamental w)
    ⟨presentedToFundamental_injective w,presentedToFundamental_surjective w⟩

theorem presentationTheorem : PresentationTheoremObligation w :=
  ⟨presentedToFundamental_injective w,presentedToFundamental_surjective w⟩

end

open DiscreteCoverCharts
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

def DeckGroup := PresentedGroup (relatorSet w)
instance : Group (DeckGroup w) := inferInstanceAs (Group (PresentedGroup (relatorSet w)))
instance : TopologicalSpace (DeckGroup w) := ⊥
instance : DiscreteTopology (DeckGroup w) := ⟨rfl⟩

def regularGenerators : Fin k → DeckGroup w := PresentedGroup.of

theorem lift_regularGenerators : FreeGroup.lift (regularGenerators w) =
    PresentedGroup.mk (relatorSet w) := by
  apply FreeGroup.ext_hom
  intro i
  rw [FreeGroup.lift_apply_of]
  rfl

theorem regular_relators (i : Fin r) :
    FreeGroup.lift (regularGenerators w) (FreeGroup.mk (w i)) = 1 := by
  rw [lift_regularGenerators]
  exact PresentedGroup.one_of_mem ⟨i,rfl⟩

def universalCore := coveringCore w (regularGenerators w) (regular_relators w)

abbrev UniversalSpace := (universalCore w).TotalSpace

def universalBasepoint : UniversalSpace w :=
  point (universalCore w) (.inl none) (basepoint w) 1

theorem universalCovering : IsCoveringMap (universalCore w).proj := covering (universalCore w)

theorem universalCovering_surjective : Function.Surjective (universalCore w).proj :=
  fun x => ⟨⟨x,(1 : DeckGroup w)⟩,rfl⟩

theorem regular_monodromyRepresentation (a q : DeckGroup w) :
    monodromyRepresentation w (regularGenerators w) (regular_relators w)
      (presentationEquiv w a) q = a * q := by
  obtain ⟨z,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) a
  have h := DFunLike.congr_fun
    (monodromyRepresentation_comp w (regularGenerators w) (regular_relators w)) z
  rw [lift_regularGenerators] at h
  change monodromyRepresentation w (regularGenerators w) (regular_relators w)
    (freeToFundamental w z) = _ at h
  change monodromyRepresentation w (regularGenerators w) (regular_relators w)
    (presentedToFundamental w (PresentedGroup.mk _ z)) q = _
  rw [presentedToFundamental_mk,h]
  rfl

theorem regular_monodromy_bijective : Function.Bijective
    (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (universalCovering w).monodromy γ ⟨universalBasepoint w,rfl⟩) := by
  let e := fiberEquiv (universalCore w) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w (regularGenerators w) (regular_relators w))
  have h (γ : FundamentalGroup (Space w) (basepoint w)) :
      (universalCovering w).monodromy γ ⟨universalBasepoint w,rfl⟩ =
        e ((presentationEquiv w).symm γ) := by
    have hm := regular_monodromyRepresentation w ((presentationEquiv w).symm γ) 1
    rw [(presentationEquiv w).apply_symm_apply] at hm
    have he := congrArg e (hm.trans (@mul_one (DeckGroup w) _ ((presentationEquiv w).symm γ)))
    exact (e.apply_symm_apply _).symm.trans he
  have heq : (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (universalCovering w).monodromy γ ⟨universalBasepoint w,rfl⟩) =
      e ∘ (presentationEquiv w).symm := funext h
  rw [heq]
  exact e.bijective.comp (presentationEquiv w).symm.bijective

instance universalSpace_simplyConnected : SimplyConnectedSpace (UniversalSpace w) :=
  RegularCoverGeometry.simplyConnected_of_monodromy_bijective
    (universalCovering w) (universalBasepoint w) (regular_monodromy_bijective w)

end PresentationGeometry.PresentationComplex

namespace PresentationGeometry
open Set Topology
universe u
variable (G : Type u) [Group G]

theorem exists_word_presentation [Group.IsFinitelyPresented G] :
    ∃ (k r : ℕ) (w : Fin r → List (Fin k × Bool)),
      Nonempty (G ≃* PresentedGroup (PresentationComplex.relatorSet w)) := by
  classical
  obtain ⟨k,φ,hφ,S,hfin,hS⟩ := Group.IsFinitelyPresented.out (G := G)
  let := hfin.fintype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let w : Fin r → List (Fin k × Bool) := fun i => (e i).1.toWord
  have hw : PresentationComplex.relatorSet w = S := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      simpa only [w,FreeGroup.mk_toWord] using (e i).2
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      refine ⟨i,?_⟩
      change FreeGroup.mk (e i).1.toWord = x
      rw [FreeGroup.mk_toWord]
      exact congrArg Subtype.val hi
  refine ⟨k,r,w,?_⟩
  have hc : Subgroup.normalClosure (PresentationComplex.relatorSet w) = φ.ker := by
    rw [hw,hS]
  let q : PresentedGroup (PresentationComplex.relatorSet w) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact ⟨q.symm⟩

theorem exists_finite_presentation_start [Group.IsFinitelyPresented G] :
    ∃ (X : Type) (t : TopologicalSpace X),
      letI : TopologicalSpace X := t
      ∃ (cw : CWComplex (univ : Set X)),
        letI : CWComplex (univ : Set X) := cw
        T2Space X ∧ PathConnectedSpace X ∧ CWComplex.Finite (univ : Set X) ∧
        ∃ (x : X), Nonempty (G ≃* FundamentalGroup X x) ∧
          ∃ (E : Type) (tE : TopologicalSpace E),
            letI : TopologicalSpace E := tE
            ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace E := by
  obtain ⟨k,r,w,⟨eg⟩⟩ := exists_word_presentation G
  refine ⟨PresentationComplex.Space w,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,PresentationComplex.basepoint w,
    ⟨eg.trans (PresentationComplex.presentationEquiv w)⟩,
    PresentationComplex.UniversalSpace w,inferInstance,(PresentationComplex.universalCore w).proj,
    PresentationComplex.universalCovering w,PresentationComplex.universalCovering_surjective w,
    inferInstance⟩

end PresentationGeometry

end

end OAI
