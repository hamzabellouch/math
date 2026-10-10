import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPrepared
import OAI.Combinatorics.SharpRamsey.Planar.HeavyPlaneCurrent

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedHeavyPlaneInput_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedHeavyPlaneInput_2 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedHeavyPlaneInput_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedHeavyPlaneInput_4 (W : Submodule K V) : Fintype (Projectivization K W) := by
  let : Finite W := Module.finite_of_finite K
  exact Fintype.ofFinite _

def planeSupport (W : Submodule K V) (S : Finset (Projectivization K V)) :
    Finset (Projectivization K W) :=
  univ.filter (fun a => Projectivization.map W.subtype W.injective_subtype a∈S)

lemma planeSupport_image (W : Submodule K V) (S : Finset (Projectivization K V)) :
    (planeSupport W S).image (Projectivization.map W.subtype W.injective_subtype)=S∩planePoints W := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    refine mem_inter.mpr ⟨(mem_filter.mp ha).2,mem_planePoints.mpr ?_⟩
    exact (projectiveSubmoduleEquiv W a).property
  · intro hx
    obtain ⟨hS,hW⟩ := mem_inter.mp hx
    let a := (projectiveSubmoduleEquiv W).symm ⟨x,mem_planePoints.mp hW⟩
    have he : Projectivization.map W.subtype W.injective_subtype a=x :=
      congrArg Subtype.val ((projectiveSubmoduleEquiv W).apply_symm_apply _)
    exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,by simpa only [he]⟩,he⟩

lemma planeSupport_card (W : Submodule K V) (S : Finset (Projectivization K V)) :
    (planeSupport W S).card=(S∩planePoints W).card := by
  rw [←planeSupport_image,card_image_of_injective _
    (Projectivization.map_injective W.subtype W.injective_subtype)]

lemma planeSupport_incidence_le (W : Submodule K V) (S : Finset (Projectivization K V))
    (t : Projectivization K (Module.Dual K V)) :
    ((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card≤
      (S.filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card := by
  rw [←card_image_of_injective _ (Projectivization.map_injective W.subtype W.injective_subtype)]
  apply card_le_card
  intro x hx
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨ha,ht⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨(mem_filter.mp ha).2,ht⟩

theorem heavy_half (W : Submodule K V) (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (τ : ℝ)
    (hτ : 0<τ) (hA : (planeSupport W S).Nonempty)
    (hheavy : (S.card:ℝ)≤50*(planeSupport W S).card)
    (hs : (incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K) :
    ∃ T₀ : Finset (Projectivization K (Module.Dual K V)),T₀⊆T ∧ T.card≤2*T₀.card ∧
      ∀ t∈T₀,(((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
        (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)≤
          (100*τ/Nat.card K)*(planeSupport W S).card := by
  let D := fun t : Projectivization K (Module.Dual K V) =>
    (((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident
      (Projectivization.map W.subtype W.injective_subtype a) t)).card:ℝ)
  let δ := 100*τ/(Nat.card K:ℝ)
  let A := (planeSupport W S).card
  let T₀ := T.filter (fun t => D t≤δ*A)
  let B := T\T₀
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hAp : (0:ℝ)<A := by exact_mod_cast card_pos.mpr hA
  have hsub : T₀⊆T := filter_subset _ _
  have hsum : ∑ t∈T,D t≤(incidenceCount S T:ℝ) := by
    unfold incidenceCount
    push_cast
    exact sum_le_sum (fun t _ => by
      dsimp only [D]
      exact_mod_cast planeSupport_incidence_le W S t)
  have htot : ∑ t∈T,D t≤δ*A*T.card/2 := by
    apply hsum.trans (hs.trans _)
    calc
      _ ≤ τ*(50*A)*T.card/Nat.card K := by gcongr
      _ = _ := by dsimp [δ]; ring
  have hB : δ*A*B.card≤∑ t∈T,D t := by
    calc
      _ = ∑ _t∈B,δ*A := by simp; ring
      _ ≤ ∑ t∈B,D t := by
        apply sum_le_sum
        intro t ht
        have htt := (mem_sdiff.mp ht).1
        have hn := (mem_sdiff.mp ht).2
        exact (lt_of_not_ge (fun hh => hn (mem_filter.mpr ⟨htt,hh⟩))).le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (by intros; dsimp [D]; positivity)
  have hc : B.card+T₀.card=T.card := by exact card_sdiff_add_card_eq_card hsub
  have hbr : (B.card:ℝ)≤(T.card:ℝ)/2 := by
    have hp := mul_pos hδ hAp
    nlinarith [hB.trans htot]
  refine ⟨T₀,hsub,?_,fun t ht => (mem_filter.mp ht).2⟩
  have hc' : (B.card:ℝ)+T₀.card=T.card := by exact_mod_cast hc
  have := (show (T.card:ℝ)≤2*T₀.card by linarith)
  exact_mod_cast this

theorem heavy_reduction (W : Submodule K V)
    (hW : Module.finrank K W+1=Module.finrank K V)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (hTU : T⊆U) (τ b : ℝ)
    (hτ : 0<τ) (hτsmall : 100*τ/(Nat.card K:ℝ)<1)
    (hheavy : (S.card:ℝ)/50≤(S∩planePoints W).card)
    (hprod : (Nat.card K:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card)
    (hs : (incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K) :
    ∃ (h : ℕ) (T₁ U₁ : Finset (Projectivization K (Module.Dual K W))),
      1≤h ∧ h≤Nat.card K ∧ T₁.Nonempty ∧ T₁⊆U₁ ∧ h*U₁.card≤U.card ∧
      (T.card:ℝ)≤4*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) ∧
      (∀ t∈T₁,(((planeSupport W S).filter (fun a => SharpLogRamsey.Incidence.Incident a t)).card:ℝ)≤
        (100*τ/Nat.card K)*(planeSupport W S).card) ∧
      (Nat.card K:ℝ)^3*exp (-b)≤
        200*(Nat.log 2 (Nat.card K)+1:ℕ)*(planeSupport W S).card*(T₁.card:ℝ) ∧
      U₁=MultiplicityClass.domain (U.subtype (· ≠ center W hW)) (restrict W hW) h := by
  have hAp : (0:ℝ)<(planeSupport W S).card := by
    rw [planeSupport_card]
    exact (div_pos (by exact_mod_cast card_pos.mpr hS) (by norm_num)).trans_le hheavy
  have hA : (planeSupport W S).Nonempty := card_pos.mp (by exact_mod_cast hAp)
  have hh : (S.card:ℝ)≤50*(planeSupport W S).card := by rw [planeSupport_card]; linarith
  obtain ⟨T₀,hsub,hhalf,hsp⟩ := heavy_half W S T τ hτ hA hh hs
  have ht₀ : T₀.Nonempty := card_pos.mp (by have := card_pos.mpr hT; omega)
  obtain ⟨h,T₁,U₁,hh1,hhq,ht₁,htu,hcap,hsize,hsp₁,he⟩ :=
    sparse_restriction_class W hW (planeSupport W S) hA T₀ U ht₀ (hsub.trans hTU)
      (100*τ/Nat.card K) hτsmall hsp
  have hhalf' : (T.card:ℝ)≤2*T₀.card := by exact_mod_cast hhalf
  have hsize' : (T.card:ℝ)≤4*h*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) := by linarith
  refine ⟨h,T₁,U₁,hh1,hhq,ht₁,htu,hcap,hsize',hsp₁,?_,he⟩
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hsize'' : (T.card:ℝ)≤4*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ) := by
    apply hsize'.trans
    gcongr
  have hpr : (Nat.card K:ℝ)^4*exp (-b)≤
      200*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(planeSupport W S).card*(T₁.card:ℝ) := by
    apply hprod.trans
    calc
      _ ≤ (50*(planeSupport W S).card)*(4*(Nat.card K)*(Nat.log 2 (Nat.card K)+1:ℕ)*(T₁.card:ℝ)) :=
        mul_le_mul hh hsize'' (by positivity) (by positivity)
      _ = _ := by ring
  nlinarith

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
