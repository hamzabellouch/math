import Mathlib

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable (K V : Type*) [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

abbrev NZ := {v : V // v≠0}

instance nzMulAction : MulAction Kˣ (NZ V) where
  smul a v := ⟨(a:K) • (v:V),smul_ne_zero a.ne_zero v.property⟩
  one_smul v := Subtype.ext (one_smul K (v:V))
  mul_smul a b v := Subtype.ext (mul_smul (a:K) (b:K) (v:V))

instance nzContinuousConstSMul : ContinuousConstSMul Kˣ (NZ V) :=
  ⟨fun _ => (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

abbrev Space := Quotient (MulAction.orbitRel Kˣ (NZ V))
def point (v : NZ V) : Space K V := Quotient.mk _ v

lemma point_surjective : Surjective (point K V) := Quotient.mk_surjective
lemma continuous_point : Continuous (point K V) := continuous_quot_mk
lemma openQuotient_point : IsOpenQuotientMap (point K V) :=
  MulAction.isOpenQuotientMap_quotientMk

variable {K V}
lemma point_eq_iff (v w : NZ V) : point K V v=point K V w ↔
    ∃ a : K, a • (w:V)=(v:V) := by
  constructor
  · intro he
    obtain ⟨a,ha⟩ := Quotient.exact he
    exact ⟨a,congrArg Subtype.val ha⟩
  · rintro ⟨a,ha⟩
    have hane : a≠0 := by intro he; rw [he,zero_smul] at ha; exact v.property ha.symm
    apply Quotient.sound
    exact ⟨Units.mk0 a hane,Subtype.ext ha⟩

lemma point_eq_iff_dependent (v w : NZ V) : point K V v=point K V w ↔
    ¬LinearIndependent K ![(v:V),(w:V)] := by
  rw [point_eq_iff,linearIndependent_fin2]
  change (∃ a : K, a • (w:V)=(v:V)) ↔ ¬((w:V)≠0 ∧ ∀ a : K, a • (w:V)≠(v:V))
  constructor
  · rintro ⟨a,ha⟩ h
    exact h.2 a ha
  · intro h
    by_contra hn
    exact h ⟨w.property,fun a ha => hn ⟨a,ha⟩⟩

instance spaceT2 [CompleteSpace K] : T2Space (Space K V) := by
  apply (t2Space_iff_of_isOpenQuotientMap (openQuotient_point K V)).mpr
  have hc : Continuous (fun z : NZ V × NZ V => ![(z.1:V),(z.2:V)]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  convert (isOpen_setOfPred_linearIndependent (𝕜:=K) (E:=V) (ι:=Fin 2)).isClosed_compl.preimage hc using 1
  ext z
  exact point_eq_iff_dependent z.1 z.2

variable (K V)
instance spaceCompact [ProperSpace K] [FiniteDimensional K V] : CompactSpace (Space K V) := by
  let : ProperSpace V := FiniteDimensional.proper K V
  obtain ⟨c,hc⟩ := NormedField.exists_one_lt_norm K
  let r : ℝ := 1/‖c‖
  have hr : 0<r := div_pos zero_lt_one (lt_trans zero_lt_one hc)
  let C : Set V := {v | r≤‖v‖ ∧ ‖v‖≤1}
  have hC : IsCompact C := by
    have he : C=Metric.closedBall (0:V) 1 ∩ {v | r≤‖v‖} := by
      ext v
      simp only [C,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right,and_comm]
    rw [he]
    exact (isCompact_closedBall (0:V) 1).inter_right (isClosed_le continuous_const continuous_norm)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C → NZ V := fun v => ⟨v,fun he => by
    have hh := v.property.1
    rw [he,norm_zero] at hh
    exact hr.not_ge hh⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  apply Function.Surjective.compactSpace ((continuous_point K V).comp hf)
  intro q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  obtain ⟨a,ha,hlt,hle,_⟩ := rescale_to_shell hc zero_lt_one (x:=(v:V)) v.property
  let w : C := ⟨a • (v:V),hle,hlt.le⟩
  refine ⟨w,(point_eq_iff (f w) v).mpr ⟨a,rfl⟩⟩

instance spaceSecondCountable [ProperSpace K] [FiniteDimensional K V] :
    SecondCountableTopology (Space K V) := by
  let : ProperSpace V := FiniteDimensional.proper K V
  exact ContinuousConstSMul.secondCountableTopology

instance spaceMetrizable [ProperSpace K] [FiniteDimensional K V] :
    MetrizableSpace (Space K V) := inferInstance

end CriticalPercolation.LocalProjective
end
end

end OAI
