import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.DescriptionHeaders
import OAI.Combinatorics.SharpRamsey.Planar.HeavyPlaneCover
import OAI.Combinatorics.SharpRamsey.Parameters.HeavyPlaneScales

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Filter SourceScales Incidence PreparedProjectiveGeometry
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_JoinedHeavyPlanePublic_1 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedHeavyPlanePublic_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedHeavyPlanePublic_3 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Submodule K V) := Finite.of_injective
    (fun W : Submodule K V => (W:Set V)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
abbrev HeavyHeaders (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n m : ℕ) :=
  {W : Submodule K V // Module.finrank K W=3} × Fin (Nat.card K+1) × Fin (n+1) × Fin (m+1)
local instance flat_JoinedHeavyPlanePublic_4 (n m : ℕ) : Fintype (HeavyHeaders K V n m) := by
  unfold HeavyHeaders
  infer_instance
abbrev headerPlane {n m : ℕ} (j : HeavyHeaders K V n m) : Submodule K V := j.1.val
omit [Finite K] [FiniteDimensional K V] in
lemma header_rank {n m : ℕ} (j : HeavyHeaders K V n m) : Module.finrank K (headerPlane j)=3 := j.1.property
omit [Finite K] [FiniteDimensional K V] in
lemma header_codim (hV : Module.finrank K V=4) {n m : ℕ} (j : HeavyHeaders K V n m) :
    Module.finrank K (headerPlane j)+1=Module.finrank K V := by rw [header_rank,hV]
def headerDomain (hV : Module.finrank K V=4)
    (UT : Finset (Projectivization K (Module.Dual K V))) {n : ℕ}
    (j : HeavyHeaders K V n UT.card) := MultiplicityClass.domain
    (UT.subtype (· ≠ center (headerPlane j) (header_codim hV j)))
    (restrict (headerPlane j) (header_codim hV j)) j.2.1.val
def HeaderValid (hV : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (UT : Finset (Projectivization K (Module.Dual K V)))
    (n t : ℕ) (L b₁ : ℝ) (j : HeavyHeaders K V n UT.card) : Prop :=
    0<j.2.1.val ∧ 0<j.2.2.1.val ∧ 0<j.2.2.2.val ∧
    n≤50*j.2.2.1.val ∧ j.2.2.1.val≤(planeSupport (headerPlane j) U).card ∧
    j.2.2.2.val≤(headerDomain hV UT j).card ∧ j.2.1.val*(headerDomain hV UT j).card≤UT.card ∧
    (t:ℝ)≤4*j.2.1.val*L*j.2.2.2.val ∧
    (Nat.card K:ℝ)^3*exp (-b₁)≤(j.2.2.1.val:ℝ)*j.2.2.2.val ∧
    (j.2.2.1.val:ℝ)*j.2.2.2.val≤2*(Nat.card K:ℝ)^3
lemma header_card (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (n m : ℕ) :
    Nat.card (HeavyHeaders K V n m)≤Nat.card (Submodule K V)*(Nat.card K+1)*(n+1)*(m+1) := by
  dsimp only [HeavyHeaders]
  simp only [Nat.card_prod,Nat.card_fin]
  simp only [←mul_assoc]
  gcongr
  exact Nat.card_le_card_of_injective (fun x : {W : Submodule K V // Module.finrank K W=3} => x.val)
    Subtype.val_injective

theorem heavy_families {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → ∀ hV : Module.finrank K V=4,
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
    ∃ fam : HeavyHeaders K V n UT.card → Finset (Finset (Projectivization K V)),
      ∀ j, (∀ W∈fam j,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,HeaderValid hV U UT n t (Nat.log 2 (Nat.card K)+1:ℕ)
          (b+log (200*(Nat.log 2 (Nat.card K)+1:ℕ))) j →
        S⊆U → S.card=n → (planeSupport (headerPlane j) S).card=j.2.2.1.val →
        T⊆headerDomain hV UT j → T.card=j.2.2.2.val →
        (incidenceCount (planeSupport (headerPlane j) S) T:ℝ)≤100*τ*(j.2.2.1.val:ℝ)*j.2.2.2.val/Nat.card K →
        ∃ W∈fam j,(n:ℝ)/100≤(S∩W).card) ∧ ((fam j).card:ℝ)≤exp E := by
  have hC' : 1≤101*C+2 := by linarith
  have htiny : Tendsto (fun σ : ℝ => 100*C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul (100*C)
  filter_upwards [fixed_heavy_cover hη (101*C+2) hC',eventually_heavy_loss hη,
    htiny.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20)),
    eventually_ge_atTop (1:ℝ)] with σ hcover hloss htiny hσ
  intro K V _ _ _ _ _ D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  let P := scaleP σ η D R
  let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
  let L : ℝ := (Nat.log 2 (Nat.card K)+1:ℕ)
  let b₁ := b+log (200*L)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hU : (0:ℝ)<U.card := hn'.trans_le (by exact_mod_cast hnu)
  have hUT : (0:ℝ)<UT.card := ht'.trans_le (by exact_mod_cast htu)
  have hL : 0<L := by dsimp [L]; positivity
  have hP : 0<P := by
    have hh := (scale_bounds hσ hη had).2.1
    exact (rpow_pos_of_pos (by linarith : 0<σ) _).trans_le hh
  obtain ⟨hl0,hlK,hlP⟩ := hloss (Nat.card K) (Finite.card_pos) hex D R had
  change 0≤log (200*L) at hl0
  change log (200*L)≤ scaleKstar σ η D at hlK
  change log 50+log (4*L)≤P at hlP
  have hb₁ : 0≤b₁ := add_nonneg hb hl0
  have hb₁U : b₁≤(101*C+2)*scaleKstar σ η D := by
    have hK := hl0.trans hlK
    dsimp [b₁]
    nlinarith
  have htau : 100*τ≤1/20 := by
    have hp : 0≤σ^(-100*beta η) := rpow_nonneg (by linarith) _
    nlinarith
  have htauU : 100*τ≤(101*C+2)*σ^(-100*beta η) := by
    have hp : 0≤σ^(-100*beta η) := rpow_nonneg (by linarith) _
    nlinarith
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hdT : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  let J := HeavyHeaders K V n UT.card
  let plane (j : J) := headerPlane j
  have plane_rank (j : J) : Module.finrank K (plane j)=3 := header_rank j
  let dom (j : J) := headerDomain hV UT j
  let valid (j : J) := HeaderValid hV U UT n t L b₁ j
  have each (j : J) : ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,valid j → S⊆U → S.card=n → (planeSupport (plane j) S).card=j.2.2.1.val →
        T⊆dom j → T.card=j.2.2.2.val →
        (incidenceCount (planeSupport (plane j) S) T:ℝ)≤100*τ*(j.2.2.1.val:ℝ)*j.2.2.2.val/Nat.card K →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧ (caps.card:ℝ)≤exp E := by
    by_cases hv : valid j
    · obtain ⟨hj,ha,hu,hheavy,hau,htu₁,hdom,hsize,hlo,hhi⟩ := hv
      obtain ⟨caps,hs,hc,hl⟩ := hcover K V D R had hex (plane j) (plane_rank j) U (dom j) n
        j.2.2.1.val j.2.2.2.val b₁ (100*τ) ha hu (Nat.le_of_lt_succ j.2.2.1.isLt) hheavy
        hau htu₁ hb₁ hb₁U (by positivity) htauU hlo hhi
      have hA : (0:ℝ)<(planeSupport (plane j) U).card := by exact_mod_cast (ha.trans_le hau)
      have hB : (0:ℝ)<(dom j).card := by exact_mod_cast (hu.trans_le htu₁)
      have hsmall : (planeSupport (plane j) U).card≤U.card := by
        rw [planeSupport_card]; exact card_le_card inter_subset_left
      obtain ⟨hd₁,hd₂⟩ := heavy_domain_gaps U.card UT.card (planeSupport (plane j) U).card (dom j).card
        n t j.2.2.1.val j.2.2.2.val j.2.1.val L hU hUT hn' ht' (by exact_mod_cast ha)
        (by exact_mod_cast hu) (by exact_mod_cast hj) hL hA hB (by exact_mod_cast hsmall)
        (by exact_mod_cast hheavy) (by exact_mod_cast hdom) hsize
      have hlen : log ((caps.card:ℝ)+1)≤E := by
        apply hl.trans
        have hqP : 0≤(Nat.card K:ℝ)*P := mul_nonneg hq.le hP.le
        have hh := mul_le_mul_of_nonneg_left (add_le_add hd₁ hd₂) hqP
        have hll := mul_le_mul_of_nonneg_left hlP hqP
        have hadd := mul_nonneg hqP (add_nonneg hd hdT)
        dsimp only [E]
        nlinarith
      refine ⟨caps,hs,fun S T _ => hc S T,?_⟩
      have he := exp_le_exp.mpr hlen
      rw [exp_log (by positivity)] at he
      linarith
    · refine ⟨∅,by simp,?_,?_⟩
      · intro S T hj; exact (hv hj).elim
      · simp only [card_empty,Nat.cast_zero]; exact (exp_pos _).le
  choose fam hf using each
  exact ⟨fam,hf⟩

theorem public_heavy_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V : Type) [Field K] [Finite K]
      [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ D R,Admissible σ η D R → exp σ=(Nat.card K:ℝ) → Module.finrank K V=4 →
    ∀ (U : Finset (Projectivization K V))
      (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
        (Nat.card K:ℝ)^4*exp (-b)≤(n:ℝ)*t →
        (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/Nat.card K →
        (∃ W : Submodule K V,Module.finrank K W=3 ∧ (n:ℝ)/50≤(S∩planePoints W).card) →
        ∃ W∈caps,(n:ℝ)/100≤(S∩W).card) ∧
      (caps.card:ℝ)≤(Nat.card (Submodule K V):ℝ)*(Nat.card K+1:ℕ)*(n+1:ℕ)*(UT.card+1:ℕ)*exp E := by
  have htiny : Tendsto (fun σ : ℝ => 100*C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul (100*C)
  filter_upwards [heavy_families hη C hC,
    htiny.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))] with σ hf htiny
  intro K V _ _ _ _ _ D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  let P := scaleP σ η D R
  let E := 4000*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)
  let L : ℝ := (Nat.log 2 (Nat.card K)+1:ℕ)
  let b₁ := b+log (200*L)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hL : 0<L := by dsimp [L]; positivity
  have htau : 100*τ≤1/20 := by linarith
  let J := HeavyHeaders K V n UT.card
  let plane (j : J) := headerPlane j
  let dom (j : J) := headerDomain hV UT j
  let valid (j : J) := HeaderValid hV U UT n t L b₁ j
  obtain ⟨fam,hfam⟩ := hf K V D R had hex hV U UT n t b τ hn ht hnu htu hb hbu hτ hτu
  have hsize (j : J) := (hfam j).1
  have hcapture (j : J) := (hfam j).2.1
  have hcount (j : J) := (hfam j).2.2
  let caps := (univ : Finset J).biUnion fam
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hW
    exact hsize j W hj
  · intro S T hSU hSn hTU hTt hprod hsparse hheavy
    obtain ⟨W,hW,hheavy⟩ := hheavy
    have hcodim : Module.finrank K W+1=Module.finrank K V := by rw [hW,hV]
    have hτone : 100*τ/(Nat.card K:ℝ)<1 := by
      apply (div_lt_iff₀ hq).mpr
      have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)
      linarith
    obtain ⟨h,T₁,U₁,hh1,hhq,hT₁,hT₁U,hU₁,hsize₁,hsp₁,hprod₁,hdom₁⟩ :=
      heavy_reduction W hcodim S (card_pos.mp (by omega)) T UT (card_pos.mp (by omega)) hTU τ b
        hτ hτone (by rwa [hSn]) (by rwa [hSn,hTt]) (by rwa [hSn,hTt])
    have ha : (planeSupport W S).card≤n := by rw [planeSupport_card,←hSn]; exact card_le_card inter_subset_left
    have hTUcard : T₁.card≤UT.card := by
      have hh := card_le_card hT₁U
      exact hh.trans ((Nat.le_mul_of_pos_left _ hh1).trans hU₁)
    let j : J := (⟨W,hW⟩,⟨h,by omega⟩,⟨(planeSupport W S).card,by omega⟩,⟨T₁.card,by omega⟩)
    have hpj : headerPlane j=W := rfl
    have hdj : headerDomain hV UT j=U₁ := hdom₁.symm
    have hsp : (incidenceCount (planeSupport W S) T₁:ℝ)≤
        100*τ*((planeSupport W S).card:ℝ)*T₁.card/Nat.card K := by
      unfold incidenceCount
      push_cast
      calc
        _ ≤ ∑ _t∈T₁,(100*τ/Nat.card K)*(planeSupport W S).card := sum_le_sum hsp₁
        _ = _ := by simp; ring
    have hsp20 : (incidenceCount (planeSupport W S) T₁:ℝ)≤
        ((planeSupport W S).card:ℝ)*T₁.card/(20*Nat.card K) := by
      apply hsp.trans
      convert mul_le_mul_of_nonneg_right htau
        (by positivity : 0≤((planeSupport W S).card:ℝ)*T₁.card/(Nat.card K:ℝ)) using 1 <;> ring
    have hupper := sparse_product_bound_two (n:=0) (by simpa using hW) (planeSupport W S) T₁ hsp20
    have hlo : (Nat.card K:ℝ)^3*exp (-b₁)≤((planeSupport W S).card:ℝ)*T₁.card := by
      have hexp : exp (-b₁)=exp (-b)/(200*L) := by
        dsimp only [b₁]
        rw [neg_add,exp_add,exp_neg (log (200*L)),exp_log (by positivity)]
        ring
      rw [hexp,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<200*L)).mpr
      dsimp only [L]
      nlinarith [hprod₁]
    have hv : valid j := by
      dsimp only [valid,HeaderValid]
      rw [hdj]
      dsimp only [j,headerPlane]
      refine ⟨by omega,?_,card_pos.mpr hT₁,?_,card_le_card (planeSupport_mono W hSU),
        card_le_card hT₁U,hU₁,?_,hlo,?_⟩
      · have hc := hheavy
        rw [←planeSupport_card] at hc
        have := div_pos hn' (by norm_num : (0:ℝ)<50)
        exact_mod_cast this.trans_le hc
      · rw [←planeSupport_card] at hheavy
        have hh : (n:ℝ)≤50*(planeSupport W S).card := by linarith
        exact_mod_cast hh
      · simpa only [hTt] using hsize₁
      · simpa using hupper
    obtain ⟨E,hE,hcap⟩ := hcapture j S T₁ hv hSU hSn rfl (by rwa [hdj]) rfl (by simpa only [j,headerPlane] using hsp)
    exact ⟨E,mem_biUnion.mpr ⟨j,mem_univ _,hE⟩,hcap⟩
  · have hsum : (caps.card:ℝ)≤∑ j : J,((fam j).card:ℝ) := by exact_mod_cast (card_biUnion_le (s:=(univ:Finset J)) (t:=fam))
    apply hsum.trans
    calc
      _ ≤ ∑ _j : J,exp E := sum_le_sum (fun j _ => hcount j)
      _ = (Fintype.card J:ℝ)*exp E := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        have hh := header_card K V n UT.card
        rw [Nat.card_eq_fintype_card] at hh
        exact_mod_cast hh

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
