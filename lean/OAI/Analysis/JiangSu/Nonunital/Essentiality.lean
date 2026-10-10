import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI


noncomputable section
namespace NonunitalSI
open scoped ComplexOrder

section Nontrivial

variable {A : Type*} [NonUnitalCStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma left_identity_isStarProjection (u : A) (hu : ∀ a : A, u*a=a) :
    IsStarProjection u := by
  have hr (a : A) : a*star u=a := by
    simpa only [star_mul, star_star] using congrArg star (hu (star a))
  have hs : star u=u := (hu (star u)).symm.trans (hr u)
  exact ⟨hu u, hs⟩

lemma unitization_action_faithful
    (hprojectionless : ∀ p : A, IsStarProjection p → p=0)
    (x : Unitization ℂ A) (hx : ∀ a : A, x*Unitization.inr a=0) : x=0 := by
  have he (a : A) : x.fst • a+x.snd*a=0 := by
    simpa only [Unitization.snd_mul, Unitization.fst_inr, Unitization.snd_inr,
      zero_smul, add_zero, Unitization.snd_zero] using congrArg (fun z : Unitization ℂ A => z.snd) (hx a)
  by_cases h : x.fst=0
  · have hz : x.snd*star x.snd=0 := by simpa only [h,zero_smul,zero_add] using he (star x.snd)
    have hz' : x.snd=0 := (CStarRing.mul_star_self_eq_zero_iff _).mp hz
    exact Unitization.ext h hz'
  · let u : A := (-x.fst⁻¹) • x.snd
    have hu (a : A) : u*a=a := by
      have ha : x.snd*a=-(x.fst • a) := eq_neg_of_add_eq_zero_right (he a)
      simp only [u,smul_mul_assoc,ha,smul_neg,smul_smul]
      simp [h]
    have hz := hprojectionless u (left_identity_isStarProjection u hu)
    have hh : ∀ a : A,a=0 := by intro a; simpa only [hz,zero_mul] using (hu a).symm
    obtain ⟨a,ha⟩ := exists_ne (0 : A)
    exact False.elim (ha (hh a))

lemma unitization_representation_injective {D : Type*} [CStarAlgebra D]
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I=⊥ ∨ I=⊤)
    (hprojectionless : ∀ p : A, IsStarProjection p → p=0)
    (π : Unitization ℂ A →⋆ₐ[ℂ] D)
    (hnonzero : ∃ a : A, π (Unitization.inr a)≠0) : Function.Injective π := by
  let ρ : A →⋆ₙₐ[ℂ] D := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hc : IsClosed (TwoSidedIdeal.ker ρ : Set A) := by
    have he : (TwoSidedIdeal.ker ρ : Set A)={a : A | ρ a=0} := by
      ext a; exact TwoSidedIdeal.mem_ker ρ
    rw [he]
    have hρ : LipschitzWith 1 ρ := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [NNReal.coe_one,one_mul,dist_eq_norm,←map_sub] using
        (NonUnitalStarAlgHom.norm_apply_le ρ (a-b))
    exact isClosed_eq hρ.continuous continuous_const
  have hfaith : Function.Injective ρ := by
    rcases hsimple (TwoSidedIdeal.ker ρ) hc with hb|ht
    · exact (TwoSidedIdeal.ker_eq_bot ρ).mp hb
    · obtain ⟨a,ha⟩ := hnonzero
      have hm : a∈TwoSidedIdeal.ker ρ := ht.symm ▸ TwoSidedIdeal.mem_top A
      exact (ha ((TwoSidedIdeal.mem_ker ρ).mp hm)).elim
  apply (injective_iff_map_eq_zero π).mpr
  intro x hx
  apply unitization_action_faithful hprojectionless x
  intro a
  let y : A := (x*Unitization.inr a).snd
  have hy : (Unitization.inr y : Unitization ℂ A)=x*Unitization.inr a := by
    apply Unitization.ext
    · simp only [Unitization.fst_inr,Unitization.fst_mul,mul_zero]
    · rfl
  have hρ : ρ y=ρ 0 := by
    change π (Unitization.inr y)=π (Unitization.inr 0)
    rw [hy,map_mul,hx,zero_mul,Unitization.inr_zero,map_zero]
  rw [←hy,hfaith hρ,Unitization.inr_zero]

end Nontrivial


open Pureness CurrentMain DirectComparison NonunitalGamma Filter Topology
open scoped ComplexOrder ENNReal

section TraceEstimate
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma traceTwoNorm_relative_factorization {I : Type*} [Fintype I]
    (τ : TracialState B) (q c u : B) (hq : ‖q‖≤1) (hc : ‖c‖≤1)
    (X Y : I → B) :
    traceTwoNorm τ q≤traceTwoNorm τ (1-u)+‖u-∑ i,X i*c*Y i‖+
      (∑ i,‖X i‖*‖Y i‖)*traceTwoNorm τ (q*c)+
      ∑ i,‖q*X i-X i*q‖*‖Y i‖ := by
  let S : B := ∑ i,X i*c*Y i
  have he : q=q*(1-u)+q*(u-S)+∑ i,q*(X i*c*Y i) := by
    rw [←Finset.mul_sum]
    dsimp [S]
    noncomm_ring
  have hfirst : traceTwoNorm τ (q*(1-u))≤traceTwoNorm τ (1-u) :=
    (traceTwoNorm_mul_left τ _ _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hq (traceTwoNorm_nonneg τ (1-u)))
  have hsecond : traceTwoNorm τ (q*(u-S))≤‖u-S‖ :=
    (traceTwoNorm_le_norm τ _).trans ((norm_mul_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq (norm_nonneg (u-S))))
  have hterm (i : I) : traceTwoNorm τ (q*(X i*c*Y i))≤
      (‖X i‖*‖Y i‖)*traceTwoNorm τ (q*c)+‖q*X i-X i*q‖*‖Y i‖ := by
    have hid : q*(X i*c*Y i)=X i*(q*c)*Y i+(q*X i-X i*q)*c*Y i := by noncomm_ring
    have hmain : traceTwoNorm τ (X i*(q*c)*Y i)≤(‖X i‖*‖Y i‖)*traceTwoNorm τ (q*c) := by
      calc
        _≤‖Y i‖*traceTwoNorm τ (X i*(q*c)) := traceTwoNorm_mul_right τ _ _
        _≤‖Y i‖*(‖X i‖*traceTwoNorm τ (q*c)) :=
          mul_le_mul_of_nonneg_left (traceTwoNorm_mul_left τ _ _) (norm_nonneg _)
        _=(‖X i‖*‖Y i‖)*traceTwoNorm τ (q*c) := by ring
    have herr : traceTwoNorm τ ((q*X i-X i*q)*c*Y i)≤‖q*X i-X i*q‖*‖Y i‖ := by
      calc
        _≤‖(q*X i-X i*q)*c*Y i‖ := traceTwoNorm_le_norm τ _
        _≤(‖q*X i-X i*q‖*‖c‖)*‖Y i‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _≤‖q*X i-X i*q‖*‖Y i‖ := mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hc (norm_nonneg (q*X i-X i*q))) (norm_nonneg _)
    rw [hid]
    exact (traceTwoNorm_add_le τ _ _).trans (add_le_add hmain herr)
  calc
    traceTwoNorm τ q≤traceTwoNorm τ (q*(1-u))+traceTwoNorm τ (q*(u-S))+
        traceTwoNorm τ (∑ i,q*(X i*c*Y i)) := by
      conv_lhs => rw [he]
      exact (traceTwoNorm_add_le τ _ _).trans (add_le_add (traceTwoNorm_add_le τ _ _) le_rfl)
    _≤traceTwoNorm τ (1-u)+‖u-S‖+
        ∑ i,((‖X i‖*‖Y i‖)*traceTwoNorm τ (q*c)+‖q*X i-X i*q‖*‖Y i‖) :=
      add_le_add (add_le_add hfirst hsecond)
        ((traceTwoNorm_sum_le _ τ _).trans (Finset.sum_le_sum fun i _ => hterm i))
    _=_ := by rw [Finset.sum_add_distrib,←Finset.sum_mul]; simp only [S,add_assoc]

end TraceEstimate

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma ideal_factorization_through_unitization [Nontrivial A]
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (c : Unitization ℂ A) (hc0 : c≠0) (u : A) {ε : ℝ} (hε : 0<ε) :
    ∃ (m : ℕ) (X Y : Fin m → Unitization ℂ A),
      ‖Unitization.inr u-∑ i,X i*c*Y i‖<ε := by
  obtain ⟨a,ha⟩ : ∃ a : A,c*Unitization.inr a≠0 := by
    by_contra! h
    exact hc0 (unitization_action_faithful hprojectionless c h)
  let z : Unitization ℂ A := c*Unitization.inr a
  have hz0 : z.fst=0 := by simp only [z,Unitization.fst_mul,Unitization.fst_inr,mul_zero]
  have hz : (Unitization.inr z.snd : Unitization ℂ A)=z := Unitization.ext hz0.symm rfl
  let b : A := star z.snd*z.snd
  have hb : 0≤b := star_mul_self_nonneg _
  have hb0 : b≠0 := by
    intro hb0
    have hz' := (CStarRing.star_mul_self_eq_zero_iff z.snd).mp hb0
    exact ha (by change z=0; rw [←hz,hz',Unitization.inr_zero])
  have hu : u∈closure (Set.range (finiteIdealSum b)) := by
    rw [finiteIdealSum_dense hsimple hb hb0]
    exact Set.mem_univ _
  obtain ⟨v,⟨l,hl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  let X : Fin l.length → Unitization ℂ A := fun i => Unitization.inr (l.get i).1*star z
  let Y : Fin l.length → Unitization ℂ A := fun i => Unitization.inr a*Unitization.inr (l.get i).2
  refine ⟨l.length,X,Y,?_⟩
  have hterm (p : A×A) : (Unitization.inr (p.1*b*p.2) : Unitization ℂ A)=
      (Unitization.inr p.1*star z)*c*(Unitization.inr a*Unitization.inr p.2) := by
    simp only [b,Unitization.inr_mul,Unitization.inr_star,hz]
    dsimp [z]
    noncomm_ring
  have hsum : (Unitization.inr (finiteIdealSum b l) : Unitization ℂ A)=∑ i,X i*c*Y i := by
    change (Unitization.inrHom ℂ ℂ A)
      ((l.map (fun p => p.1*b*p.2)).sum)=_
    rw [map_list_sum]
    change ((l.map (fun p => p.1*b*p.2)).map
      (fun a => (Unitization.inr a : Unitization ℂ A))).sum=_
    simp only [List.map_map,Function.comp_def,hterm]
    rw [←List.sum_ofFn]
    congr 1
    change l.map (fun p => (Unitization.inr p.1*star z)*c*(Unitization.inr a*Unitization.inr p.2))=
      List.ofFn ((fun p : A×A => (Unitization.inr p.1*star z)*c*(Unitization.inr a*Unitization.inr p.2)) ∘ l.get)
    rw [←List.map_ofFn,List.ofFn_get]
  rw [←hsum,←Unitization.inr_sub,Unitization.norm_inr,hl]
  simpa only [dist_eq_norm,norm_sub_rev] using hv

end NonunitalSI

end

end OAI
