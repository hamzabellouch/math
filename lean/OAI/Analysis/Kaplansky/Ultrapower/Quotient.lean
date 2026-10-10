import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue
import OAI.Analysis.Kaplansky.Ultrapower.QuasiFinite

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma q_eq_of_null_sub {a b : A} (h : V.IsNull (a-b)) : V.q a=V.q b := by
  apply V.val_eq_of_null_sub (star_mul_self_nonneg _) (star_mul_self_nonneg _)
  have h₁ := V.null_mul_left h (star a)
  have h₂ := V.null_mul_right (V.null_star h) b
  convert V.null_add h₁ h₂ using 1
  simp only [star_sub]
  noncomm_ring

def quotQ : V.FaithfulQuotient → ℝ := Quotient.lift (s := V.nullIdeal.submodule.quotientRel) V.q (fun a b h =>
  V.q_eq_of_null_sub (by exact (Submodule.quotientRel_def V.nullIdeal.submodule).mp h))

@[simp] lemma quotQ_map (a : A) : V.quotQ (V.quotientHom a)=V.q a := rfl

lemma quotQ_nonneg (x : V.FaithfulQuotient) : 0≤V.quotQ x := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact V.q_nonneg a

@[simp] lemma quotQ_zero : V.quotQ 0=0 := V.q_zero
@[simp] lemma quotQ_one : V.quotQ 1=1 := by change V.val (star 1*1)=1; simpa using V.one

@[simp] lemma quotQ_star (x : V.FaithfulQuotient) : V.quotQ (star x)=V.quotQ x := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact V.q_star a

lemma quotQ_eq_zero (x : V.FaithfulQuotient) : V.quotQ x=0 ↔ x=0 := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact (V.nullIdeal.mk_eq_zero a).symm

lemma quotQ_bound (x : V.FaithfulQuotient) : V.quotQ x≤‖x‖^2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min 1 (ε/(2*‖x‖+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨a,ha,hn⟩ := V.nullIdeal.norm_mk_lt x hδ
  change V.quotientHom a=x at ha
  have hq := V.q_bound a
  rw [← V.quotQ_map a,ha] at hq
  have hδ1 : δ≤1 := min_le_left ..
  have hd : δ*(2*‖x‖+1)≤ε := by
    exact (le_div_iff₀ (by positivity : 0<2*‖x‖+1)).mp (min_le_right ..)
  nlinarith [norm_nonneg a,norm_nonneg x]

lemma quotQ_projection_lift {a : A} (ha : 0≤a) (hp : IsStarProjection (V.quotientHom a)) :
    V.quotQ (V.quotientHom a)=V.val a := by
  change V.val (star a*a)=V.val a
  apply V.val_eq_of_null_sub (star_mul_self_nonneg a) ha
  apply (V.nullIdeal.mk_eq_zero _).mp
  change V.quotientHom (star a*a-a)=0
  simp only [map_sub,map_mul,map_star,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,sub_self]

lemma quotQ_partial_projection {v : V.FaithfulQuotient}
    (hv : IsStarProjection (star v*v)) : V.quotQ (star v*v)=V.quotQ v := by
  obtain ⟨a,ha⟩ := V.nullIdeal.mk_surjective v
  change V.quotientHom a=v at ha
  subst v
  have hp : IsStarProjection (V.quotientHom (star a*a)) := by simpa only [map_mul,map_star] using hv
  have h := V.quotQ_projection_lift (star_mul_self_nonneg a) hp
  simpa only [map_mul,map_star,quotQ_map,q] using h

lemma projection_add {B : Type*} [CStarAlgebra B] {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p*q=0) : IsStarProjection (p+q) := by
  have hqp : q*p=0 := by simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero] using congrArg star hpq
  refine ⟨?_,hp.isSelfAdjoint.add hq.isSelfAdjoint⟩
  change (p+q)*(p+q)=p+q
  simp only [add_mul,mul_add,hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq,hqp,add_zero,zero_add]

lemma selfAdjoint_lift (x : V.FaithfulQuotient) (hx : IsSelfAdjoint x) :
    ∃ a : A, IsSelfAdjoint a ∧ V.quotientHom a=x := by
  obtain ⟨b,hb⟩ := V.nullIdeal.mk_surjective x
  change V.quotientHom b=x at hb
  refine ⟨(2:ℝ)⁻¹ • (b+star b),?_,?_⟩
  · change star ((2:ℝ)⁻¹ • (b+star b))=(2:ℝ)⁻¹ • (b+star b)
    simp only [star_smul,star_trivial,star_add,star_star,add_comm]
  · have hs : V.quotientHom ((2:ℝ)⁻¹ • (b+star b)) = (2:ℝ)⁻¹ • V.quotientHom (b+star b) :=
      V.quotientHom.toAlgHom.map_smul_of_tower _ _
    rw [hs,map_add,map_star,hb,hx.star_eq,← two_smul ℝ x,smul_smul]
    norm_num

open scoped CStarAlgebra in
lemma quotQ_projection_add [Nontrivial A] {p q : V.FaithfulQuotient}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p*q=0) :
    V.quotQ (p+q)=V.quotQ p+V.quotQ q := by
  obtain ⟨a,ha,he⟩ := V.selfAdjoint_lift (p-q) (hp.isSelfAdjoint.sub hq.isSelfAdjoint)
  have hph := CFC.posPart_negPart_unique (a:=p-q) rfl hpq hp.nonneg hq.nonneg
  have hmapP : V.quotientHom a⁺=p := by
    rw [CFC.posPart_def,NonUnitalStarAlgHomClass.map_cfcₙ V.quotientHom (fun t : ℝ => t⁺) a (ha:=ha) (hφa:=ha.map V.quotientHom),← CFC.posPart_def,he,hph.1]
  have hmapN : V.quotientHom a⁻=q := by
    rw [CFC.negPart_def,NonUnitalStarAlgHomClass.map_cfcₙ V.quotientHom (fun t : ℝ => t⁻) a (ha:=ha) (hφa:=ha.map V.quotientHom),← CFC.negPart_def,he,hph.2]
  have hP : IsStarProjection (V.quotientHom a⁺) := hmapP ▸ hp
  have hN : IsStarProjection (V.quotientHom a⁻) := hmapN ▸ hq
  have hPN : IsStarProjection (V.quotientHom (a⁺+a⁻)) := by
    rw [map_add,hmapP,hmapN]; exact projection_add hp hq hpq
  have hval := V.add_commute (CFC.posPart_nonneg a).isSelfAdjoint (CFC.negPart_nonneg a).isSelfAdjoint
    (show Commute a⁺ a⁻ from (CFC.posPart_mul_negPart a).trans (CFC.negPart_mul_posPart a).symm)
  rw [← V.quotQ_projection_lift (CFC.posPart_nonneg a) hP,
    ← V.quotQ_projection_lift (CFC.negPart_nonneg a) hN,
    ← V.quotQ_projection_lift (add_nonneg (CFC.posPart_nonneg a) (CFC.negPart_nonneg a)) hPN,
    map_add,hmapP,hmapN] at hval
  exact hval


end KaplanskyConsequences.QuasiValue

end

end OAI
