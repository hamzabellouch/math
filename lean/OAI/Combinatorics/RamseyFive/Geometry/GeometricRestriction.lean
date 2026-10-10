import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def Domain (f : V→ₗ[K]W) := {p : ℙ K V // f p.rep≠0}

noncomputable def image (f : V→ₗ[K]W) (p : Domain f) : ℙ K W :=
  Projectivization.mk K (f p.val.rep) p.property

lemma image_eq_iff (f : V→ₗ[K]W) (p : Domain f) (b : ℙ K W) :
    image f p=b ↔ ∃ a : Kˣ,a • f p.val.rep=b.rep := by
  change Projectivization.mk K (f p.val.rep) p.property=b ↔ _
  conv_lhs => rw [←b.mk_rep,eq_comm,Projectivization.mk_eq_mk_iff]

noncomputable def normalized (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) : {v : V // f v=b.rep} :=
  ⟨(image_eq_iff f p.val b |>.mp p.property).choose • p.val.val.rep,by
    rw [LinearMap.map_smul_of_tower]
    exact (image_eq_iff f p.val b |>.mp p.property).choose_spec⟩

lemma normalized_nonzero (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) : (normalized f b p).val≠0 := by
  intro h
  have hh := (normalized f b p).property
  rw [h,map_zero] at hh
  exact b.rep_nonzero hh.symm

lemma mk_normalized (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) :
    Projectivization.mk K (normalized f b p).val (normalized_nonzero f b p)=p.val.val := by
  rw [←p.val.val.mk_rep,Projectivization.mk_eq_mk_iff]
  exact ⟨_,rfl⟩

lemma normalized_injective (f : V→ₗ[K]W) (b : ℙ K W) :
    Function.Injective (normalized f b) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  rw [←mk_normalized f b p,←mk_normalized f b q]
  have hh := congrArg Subtype.val hpq
  congr 1

lemma affine_fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (w : W) : Nat.card {v : V // f v=w}≤Nat.card f.ker := by
  classical
  let : Finite V := Module.finite_of_finite K
  by_cases h : ∃v,f v=w
  · obtain ⟨v₀,hv₀⟩:=h
    let g : {v : V // f v=w}→f.ker := fun v=>⟨v.val-v₀,by
      rw [LinearMap.mem_ker,map_sub,v.property,hv₀,sub_self]⟩
    apply Nat.card_le_card_of_injective g
    intro a b hab
    apply Subtype.ext
    have hh := congrArg Subtype.val hab
    change a.val-v₀=b.val-v₀ at hh
    have hhh := congrArg (fun x : V=>x+v₀) hh
    simpa only [sub_add_cancel] using hhh
  · have hi : IsEmpty {v : V // f v=w} := ⟨fun v=>h ⟨v.val,v.property⟩⟩
    let := hi
    simp

theorem fiber_card_le [Finite K] [FiniteDimensional K V]
    (f : V→ₗ[K]W) (b : ℙ K W) :
    Nat.card {p : Domain f // image f p=b}≤(Nat.card K)^(finrank K f.ker) := by
  let : Finite V := Module.finite_of_finite K
  have hh := (Nat.card_le_card_of_injective (normalized f b) (normalized_injective f b)).trans
    (affine_fiber_card_le f b.rep)
  have hn : Nat.card f.ker=(Nat.card K)^(finrank K f.ker) :=
    Module.natCard_eq_pow_finrank (K:=K)
  exact hh.trans_eq hn

theorem dual_restriction_fiber_card_le [Finite K] [FiniteDimensional K V]
    (U : Submodule K V) (b : ℙ K (Dual K U)) :
    Nat.card {p : Domain U.dualRestrict // image U.dualRestrict p=b}≤
      (Nat.card K)^(finrank K V-finrank K U) := by
  have hh := fiber_card_le U.dualRestrict b
  have hr := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hk : finrank K U.dualRestrict.ker=finrank K V-finrank K U := by
    change finrank K U.dualAnnihilator=_
    omega
  rwa [hk] at hh

end

open Module ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_restriction (U : Submodule K V) (x : ℙ K U)
    (p : Domain U.dualRestrict) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p.val ↔
      Incident x (image U.dualRestrict p) := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident image
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker,Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K
    (U.dualRestrict p.val.rep) p.property
  rw [←ha]
  simp only [Units.smul_def,LinearMap.smul_apply,Submodule.dualRestrict_apply,
    smul_eq_mul,mul_eq_zero,Units.ne_zero,false_or,Submodule.subtype_apply]

lemma incident_of_zero_restriction (U : Submodule K V) (x : ℙ K U)
    (p : ℙ K (Dual K V)) (hp : U.dualRestrict p.rep=0) :
    Incident (Projectivization.map U.subtype U.injective_subtype x) p := by
  induction x using Projectivization.ind with | h v hv =>
  rw [Projectivization.map_mk]
  unfold Incident
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  exact congrArg (fun f : Dual K U=>f v) hp

lemma restriction_nonzero_of_degree_lt
    (U : Submodule K V) (S : Finset (ℙ K U)) (p : ℙ K (Dual K V))
    (h : (S.filter fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p).card<S.card) :
    U.dualRestrict p.rep≠0 := by
  intro hp
  have he : S.filter (fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p)=S := by
    apply Finset.filter_eq_self.mpr
    intro x _
    exact incident_of_zero_restriction U x p hp
  rw [he] at h
  exact lt_irrefl _ h

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.DyadicLifts
open scoped Classical BigOperators
variable {A B : Type*}

noncomputable def multiplicity (f : A→B) (T : Finset A) (b : B) : ℕ :=
  (T.filter fun a=> f a=b).card

noncomputable def bin (f : A→B) (T : Finset A) (k : ℕ) : Finset A :=
  T.filter fun a=> Nat.log 2 (multiplicity f T (f a))=k

noncomputable def restrictions (f : A→B) (T : Finset A) (k : ℕ) : Finset B :=
  (bin f T k).image f

noncomputable def enclosure (f : A→B) (U : Finset A) (l : ℕ) : Finset B :=
  (U.image f).filter fun b=> l ≤ multiplicity f U b

lemma multiplicity_pos (f : A→B) (T : Finset A) {a : A} (ha : a∈T) :
    0 < multiplicity f T (f a) :=
  Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩

lemma multiplicity_mono (f : A→B) {T U : Finset A} (hTU : T⊆U) (b : B) :
    multiplicity f T b ≤ multiplicity f U b :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)

lemma bin_fiber (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    multiplicity f (bin f T k) b=multiplicity f T b := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hak := (Finset.mem_filter.mp ha).2
  unfold multiplicity
  congr 1
  ext x
  simp only [bin,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx,_⟩,he⟩;exact ⟨hx,he⟩
  · rintro ⟨hx,he⟩;exact ⟨⟨hx,by rw [he];exact hak⟩,he⟩

lemma bin_multiplicity_bounds (f : A→B) (T : Finset A) (k : ℕ) {b : B}
    (hb : b∈restrictions f T k) :
    2^k ≤ multiplicity f T b ∧ multiplicity f T b < 2*(2^k) := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ha,hk⟩ := Finset.mem_filter.mp ha
  have hp := multiplicity_pos f T ha
  constructor
  · rw [←hk];exact Nat.pow_log_le_self 2 (ne_of_gt hp)
  · have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (multiplicity f T (f a))
    rw [hk,pow_succ,mul_comm] at hh
    exact hh

lemma bin_mass_bounds (f : A→B) (T : Finset A) (k : ℕ) :
    2^k*(restrictions f T k).card ≤ (bin f T k).card ∧
      (bin f T k).card ≤ 2*(2^k)*(restrictions f T k).card := by
  have he : (bin f T k).card=∑b∈restrictions f T k,multiplicity f T b := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=f) (t:=restrictions f T k)
      (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)]
    apply Finset.sum_congr rfl
    intro b hb
    exact bin_fiber f T k hb
  rw [he]
  constructor
  · calc
      _ = ∑b∈restrictions f T k,2^k := by simp [mul_comm]
      _  ≤  _ := Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).1
  · calc
      _  ≤  ∑b∈restrictions f T k,2*(2^k) :=
        Finset.sum_le_sum fun b hb=> (bin_multiplicity_bounds f T k hb).2.le
      _ = _ := by simp [mul_comm]

lemma restrictions_subset_enclosure (f : A→B) {T U : Finset A} (hTU : T⊆U) (k : ℕ) :
    restrictions f T k⊆enclosure f U (2^k) := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_image.mpr ⟨a,hTU (Finset.mem_filter.mp ha).1,rfl⟩,
    (bin_multiplicity_bounds f T k hb).1.trans (multiplicity_mono f hTU _)⟩

lemma enclosure_mass (f : A→B) (U : Finset A) (l : ℕ) :
    l*(enclosure f U l).card ≤ U.card := by
  have hs : enclosure f U l⊆U.image f := Finset.filter_subset _ _
  calc
    _ = ∑b∈enclosure f U l,l := by simp [mul_comm]
    _  ≤  ∑b∈enclosure f U l,multiplicity f U b :=
      Finset.sum_le_sum fun b hb=> (Finset.mem_filter.mp hb).2
    _  ≤  ∑b∈U.image f,multiplicity f U b :=
      Finset.sum_le_sum_of_subset hs
    _ = U.card := (Finset.card_eq_sum_card_fiberwise (fun a ha=> Finset.mem_image.mpr ⟨a,ha,rfl⟩)).symm

theorem exists_massive_bin (f : A→B) (T : Finset A) (M : ℕ)
    (hM : ∀a∈T,multiplicity f T (f a) ≤ M) :
    ∃ k ≤ Nat.log 2 M, T.card ≤ (Nat.log 2 M+1)*(bin f T k).card := by
  let keys := Finset.range (Nat.log 2 M+1)
  have maps : ∀a∈T,Nat.log 2 (multiplicity f T (f a))∈keys := by
    intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM a ha)))
  have hn : keys.Nonempty := ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hp : (0:ℝ) < keys.card := by exact_mod_cast Finset.card_pos.mpr hn
  obtain ⟨k,hk,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s:=T) (t:=keys) (f:=fun a=> Nat.log 2 (multiplicity f T (f a)))
    (b:=(T.card:ℝ)/keys.card) maps hn (by
      rw [nsmul_eq_mul,mul_div_cancel₀ _ (ne_of_gt hp)])
  refine ⟨k,Nat.le_of_lt_succ (Finset.mem_range.mp hk),?_⟩
  have hh : (T.card:ℝ) ≤ (keys.card:ℝ)*(bin f T k).card := by
    have := (div_le_iff₀ hp).mp hc
    simpa only [bin,mul_comm] using this
  have hkeys : keys.card=Nat.log 2 M+1 := Finset.card_range _
  rw [hkeys] at hh
  exact_mod_cast hh

end SharpRamseyFive.DyadicLifts

namespace SharpRamseyFive.ProjectiveRestriction
open Module DyadicLifts
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

lemma finite_lift_bound (U : Submodule K V) (T : Finset (Domain U.dualRestrict))
    (b : ℙ K (Dual K U)) :
    multiplicity (image U.dualRestrict) T b ≤ (Nat.card K)^(finrank K V-finrank K U) := by
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Finite (Domain U.dualRestrict) := by unfold Domain; infer_instance
  let f := image U.dualRestrict
  let A := T.filter fun p=>f p=b
  let g : A→{p : Domain U.dualRestrict // f p=b} := fun p=>⟨p.val,(Finset.mem_filter.mp p.prop).2⟩
  have hi : Function.Injective g := by
    intro a c hac
    have hh := congrArg (fun x : {p : Domain U.dualRestrict // f p=b}=>x.val) hac
    exact Subtype.ext hh
  have hn := Nat.card_le_card_of_injective g hi
  have he : Nat.card A=A.card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [he] at hn
  exact hn.trans (dual_restriction_fiber_card_le U b)

theorem exists_restriction_dyad (U : Submodule K V)
    (T UT : Finset (Domain U.dualRestrict)) (hTU : T⊆UT) (hT : T.Nonempty) :
    ∃ k ≤ Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U)),
      2^k ≤ (Nat.card K)^(finrank K V-finrank K U) ∧
      T.card ≤ 2*(Nat.log 2 ((Nat.card K)^(finrank K V-finrank K U))+1)*(2^k)*
        (restrictions (image U.dualRestrict) T k).card ∧
      restrictions (image U.dualRestrict) T k ⊆ enclosure (image U.dualRestrict) UT (2^k) ∧
      (2^k)*(enclosure (image U.dualRestrict) UT (2^k)).card ≤ UT.card ∧
      ∀b∈restrictions (image U.dualRestrict) T k,
        2^k ≤ multiplicity (image U.dualRestrict) T b ∧
        multiplicity (image U.dualRestrict) T b < 2*(2^k) := by
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let f := image U.dualRestrict
  have hl : ∀a∈T,multiplicity f T (f a) ≤ M := fun a _=>finite_lift_bound U T (f a)
  obtain ⟨k,hk,hc⟩ := exists_massive_bin f T M hl
  have hM : M≠0 := by
    obtain ⟨a,ha⟩ := hT
    exact ne_of_gt ((multiplicity_pos f T ha).trans_le (hl a ha))
  refine ⟨k,hk,Nat.pow_le_of_le_log hM hk,?_,
    restrictions_subset_enclosure f hTU k,enclosure_mass f UT (2^k),
    fun b hb=>bin_multiplicity_bounds f T k hb⟩
  have hm := (bin_mass_bounds f T k).2
  have hh := hc.trans (Nat.mul_le_mul_left (Nat.log 2 M+1) hm)
  simpa only [M,f,mul_assoc,mul_left_comm,mul_comm] using hh

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.FiniteRemoval
open scoped Classical BigOperators
variable {A : Type*}

theorem retain_card (T : Finset A) (d : A→ℝ) (c δ : ℝ) (hc : 0 < c)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ δ*c*T.card) :
    (1-δ)*(T.card:ℝ) ≤ (T.filter fun a=>d a ≤ c).card := by
  let G := T.filter fun a=>d a ≤ c
  let B := T.filter fun a=>c < d a
  have hpartition : G.card+B.card=T.card := by
    have he : B=T.filter (fun a=>¬d a ≤ c) := by simp only [B,not_le]
    rw [he]
    exact Finset.card_filter_add_card_filter_not _
  have hB : c*(B.card:ℝ) ≤ ∑a∈B,d a := by
    calc
      _ = ∑a∈B,c := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun a ha=>(Finset.mem_filter.mp ha).2.le
  have hBT : ∑a∈B,d a ≤ ∑a∈T,d a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a ha _=>hd a ha)
  have hcard : (G.card:ℝ)+(B.card:ℝ)=T.card := by exact_mod_cast hpartition
  have hbad : (B.card:ℝ) ≤ δ*T.card := by
    have hh := hB.trans (hBT.trans hsum)
    nlinarith
  change (1-δ)*(T.card:ℝ) ≤ (G.card:ℝ)
  nlinarith

theorem large_cell_retains_half (T : Finset A) (d : A→ℝ)
    (n s q τ : ℝ) (hq : 0 < q) (hs : 0 < s) (hτ : 0 < τ)
    (hsmall : Real.sqrt τ ≤ 1/200) (hsize : n ≤ 100*s)
    (hd : ∀a∈T,0 ≤ d a) (hsum : ∑a∈T,d a ≤ τ*n*T.card/q) :
    (T.card:ℝ)/2 ≤ (T.filter fun a=>d a ≤ Real.sqrt τ*s/q).card := by
  have hr : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hr2 := Real.sq_sqrt hτ.le
  have hc : 0 < Real.sqrt τ*s/q := div_pos (mul_pos hr hs) hq
  have hcs : τ*n/q ≤ (1/2:ℝ)*(Real.sqrt τ*s/q) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hq).mpr
    have hτn : τ*n ≤ τ*(100*s) := mul_le_mul_of_nonneg_left hsize hτ.le
    have hsτ : τ*(100*s) ≤ (1/2:ℝ)*(Real.sqrt τ*s) := by
      have hτr : τ ≤ Real.sqrt τ/200 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hτr hs.le
      nlinarith
    nlinarith
  have hh : ∑a∈T,d a ≤ (1/2:ℝ)*(Real.sqrt τ*s/q)*T.card := by
    calc
      _ ≤ τ*n*T.card/q := hsum
      _ = (τ*n/q)*T.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcs (Nat.cast_nonneg _)
  have hz := retain_card T d (Real.sqrt τ*s/q) (1/2) hc hd hh
  linarith

end SharpRamseyFive.FiniteRemoval

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def flatDegree (U : Submodule K V) (S : Finset (ℙ K U))
    (p : ℙ K (Dual K V)) : ℕ :=
  (S.filter fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p).card

noncomputable def goodLifts (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) : Finset (ℙ K (Dual K V)) :=
  T.filter fun p=>(flatDegree U S p:ℝ) ≤ κ*S.card

noncomputable def nonzeroLifts (U : Submodule K V) (T : Finset (ℙ K (Dual K V))) :
    Finset (Domain U.dualRestrict) := T.subtype fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0

lemma goodLifts_nonzero (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (hκ : κ < 1) (hS : S.Nonempty)
    {p : ℙ K (Dual K V)} (hp : p∈goodLifts U S T κ) : U.dualRestrict p.rep≠0 := by
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hcut := (Finset.mem_filter.mp hp).2
  have hdeg : (flatDegree U S p:ℝ) < S.card := by nlinarith
  apply restriction_nonzero_of_degree_lt U S p
  exact_mod_cast hdeg

lemma card_nonzeroLifts (U : Submodule K V) (T : Finset (ℙ K (Dual K V)))
    (hT : ∀p∈T,U.dualRestrict p.rep≠0) : (nonzeroLifts U T).card=T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card=T.card
  rw [Finset.card_subtype,Finset.filter_eq_self.mpr hT]

lemma nonzeroLifts_mono (U : Submodule K V) {T UT : Finset (ℙ K (Dual K V))}
    (hTU : T⊆UT) : nonzeroLifts U T⊆nonzeroLifts U UT := Finset.subtype_mono hTU

lemma card_nonzeroLifts_le (U : Submodule K V) (T : Finset (ℙ K (Dual K V))) :
    (nonzeroLifts U T).card ≤ T.card := by
  change (T.subtype (fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0)).card ≤ T.card
  rw [Finset.card_subtype]
  exact Finset.card_filter_le _ _

lemma restricted_flatDegree (U : Submodule K V) (S : Finset (ℙ K U))
    (p : Domain U.dualRestrict) :
    (S.filter fun x=>Incident x (image U.dualRestrict p)).card=flatDegree U S p.val := by
  unfold flatDegree
  congr 1
  ext x
  simp only [Finset.mem_filter,incident_restriction]

lemma restricted_degree_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ)
    {b : ℙ K (Dual K U)}
    (hb : b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k) :
    ((S.filter fun x=>Incident x b).card:ℝ) ≤ κ*S.card := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
  have hpT : p∈nonzeroLifts U (goodLifts U S T κ) := (Finset.mem_filter.mp hp).1
  have hg : p.val∈goodLifts U S T κ := Finset.mem_subtype.mp hpT
  rw [restricted_flatDegree]
  exact (Finset.mem_filter.mp hg).2

lemma reduced_incidence_bound (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) (k : ℕ) :
    (incidences S (restrictions (image U.dualRestrict)
      (nonzeroLifts U (goodLifts U S T κ)) k):ℝ) ≤
      κ*S.card*(restrictions (image U.dualRestrict)
        (nonzeroLifts U (goodLifts U S T κ)) k).card := by
  rw [incidences_eq_sum]
  calc
    _ ≤ ∑b∈restrictions (image U.dualRestrict) (nonzeroLifts U (goodLifts U S T κ)) k,
        κ*S.card := by
      apply Finset.sum_le_sum
      intro b hb
      have hh := restricted_degree_bound U S T κ k hb
      simpa only [Finset.sum_boole,incidenceEntry] using hh
    _ = _ := by simp [mul_comm]

end

section
open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_restriction (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ : ℝ) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      2^k ≤ M ∧
      (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card ∧
      (restrictions (image U.dualRestrict) G k).Nonempty ∧
      restrictions (image U.dualRestrict) G k ⊆
        enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k) ∧
      ((enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card:ℝ)*T.card ≤
        4*L*UT.card*(restrictions (image U.dualRestrict) G k).card ∧
      n*T.card ≤ 400*L*M*S.card*(restrictions (image U.dualRestrict) G k).card := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hqpos : (0:ℝ) < Nat.card K := by linarith
  have hscard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htcard : (0:ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hκ : Real.sqrt τ/(Nat.card K) < 1 := by
    apply (div_lt_one hqpos).mpr
    linarith
  have hGcard : G.card=(goodLifts U S T (Real.sqrt τ/Nat.card K)).card :=
    card_nonzeroLifts U _ (fun p hp=>goodLifts_nonzero U S T _ hκ hS hp)
  have hhalf : (T.card:ℝ)/2 ≤ G.card := by
    rw [hGcard]
    have hh := large_cell_retains_half T (fun p=>(flatDegree U S p:ℝ))
      n S.card (Nat.card K) τ hqpos hscard hτ hsmall hsize
      (fun _ _=>Nat.cast_nonneg _) hsum
    simpa only [goodLifts,div_mul_eq_mul_div] using hh
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0:ℝ)<(T.card:ℝ)/2) hhalf)
  have hGUT : G⊆nonzeroLifts U UT :=
    nonzeroLifts_mono U ((Finset.filter_subset _ _).trans hTU)
  obtain ⟨k,hk,hkm,hm,hsub,hencl,hdyad⟩ := exists_restriction_dyad U G (nonzeroLifts U UT) hGUT hG
  have hm' : (G.card:ℝ) ≤ 2*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    exact_mod_cast hm
  have hmass : (T.card:ℝ) ≤ 4*L*(2^k)*(restrictions (image U.dualRestrict) G k).card := by
    linarith
  have h0 : (restrictions (image U.dualRestrict) G k).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hz
    have he : (restrictions (image U.dualRestrict) G k).card=0 := by omega
    rw [he,Nat.cast_zero,mul_zero] at hmass
    linarith
  refine ⟨k,hk,hkm,hmass,h0,hsub,?_,?_⟩
  · have he : (2:ℝ)^k*(enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card ≤ UT.card := by
      have hh := hencl.trans (card_nonzeroLifts_le U UT)
      exact_mod_cast hh
    have h1 := mul_le_mul_of_nonneg_left hmass
      (Nat.cast_nonneg (enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)).card)
    have h2 := mul_le_mul_of_nonneg_left he
      (by positivity : (0:ℝ) ≤ 4*L*(restrictions (image U.dualRestrict) G k).card)
    nlinarith
  · have hkm' : (2:ℝ)^k ≤ M := by exact_mod_cast hkm
    have h1 := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg T.card)
    have h2 := mul_le_mul_of_nonneg_left hmass
      (by positivity : (0:ℝ) ≤ 100*S.card)
    have h3 := mul_le_mul_of_nonneg_left hkm'
      (by positivity : (0:ℝ) ≤ 400*L*S.card*(restrictions (image U.dualRestrict) G k).card)
    nlinarith

end

open Module ProjectiveIncidence DyadicLifts FiniteRemoval
open scoped Classical LinearAlgebra.Projectivization BigOperators

lemma logarithmic_gap_of_cross {a b c d C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hC : 0 < C)
    (hcross : a*d ≤ C*c*b) :
    Real.log (a/b) ≤ Real.log (c/d)+Real.log C := by
  have hh : a/b ≤ C*(c/d) := by
    apply (div_le_iff₀ hb).mpr
    calc
      a  ≤  (C*c*b)/d := (le_div_iff₀ hd).mpr hcross
      _ = C*(c/d)*b := by ring
  have hl := Real.log_le_log (div_pos ha hb) hh
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (div_pos hc hd))] at hl
  linarith only [hl]

lemma restriction_product_loss (q n t s t₀ b L : ℝ) (D j : ℕ)
    (hq : 0 < q) (hL : 0 < L) (hjd : j ≤ D)
    (horig : q^D*Real.exp (-b) ≤ n*t)
    (hred : n*t ≤ 400*L*q^(D-j)*s*t₀) :
    q^j*Real.exp (-(b+Real.log (400*L))) ≤ s*t₀ := by
  have hpow : 0 < q^(D-j) := pow_pos hq _
  have hmul : q^(D-j)*(q^j*Real.exp (-b)) ≤ q^(D-j)*(400*L*s*t₀) := by
    have he : q^D=q^(D-j)*q^j := by rw [←pow_add,Nat.sub_add_cancel hjd]
    rw [he] at horig
    nlinarith only [horig,hred]
  have hc : q^j*Real.exp (-b) ≤ 400*L*s*t₀ := (mul_le_mul_iff_of_pos_left hpow).mp hmul
  rw [neg_add,Real.exp_add,Real.exp_neg (Real.log (400*L)),Real.exp_log (by positivity)]
  rw [←mul_assoc,mul_inv_le_iff₀ (by positivity : (0:ℝ)<400*L)]
  nlinarith only [hc]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem large_cell_pair_with_losses (U : Submodule K V) (S : Finset (ℙ K U))
    (T UT : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hTU : T⊆UT) (n τ b : ℝ) (hn : 0 < n) (hτ : 0 < τ) (hsmall : Real.sqrt τ ≤ 1/200)
    (hsize : n ≤ 100*S.card)
    (horig : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b) ≤ n*T.card)
    (hsum : ∑p∈T,(flatDegree U S p:ℝ) ≤ τ*n*T.card/(Nat.card K)) :
    let M := (Nat.card K)^(finrank K V-finrank K U)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
    ∃ k ≤ Nat.log 2 M,
      let T₀ := restrictions (image U.dualRestrict) G k
      let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K U)*Real.exp (-(b+Real.log (400*L))) ≤ (S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ) ≤ (Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ) ≤ Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card) ≤ Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      ∀u v : ℝ,0 < u → u ≤ v →
        Real.log (u/S.card) ≤ Real.log (v/n)+Real.log 100 := by
  dsimp only
  let M := (Nat.card K)^(finrank K V-finrank K U)
  let L := Nat.log 2 M+1
  let G := nonzeroLifts U (goodLifts U S T (Real.sqrt τ/Nat.card K))
  obtain ⟨k,hk,_,hm,hT₀,hsub,hgap,hprod⟩ :=
    large_cell_restriction U S T UT hS hT hTU n τ hτ hsmall hsize hsum
  let T₀ := restrictions (image U.dualRestrict) G k
  let UT₀ := enclosure (image U.dualRestrict) (nonzeroLifts U UT) (2^k)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  have hL : (0:ℝ)<L := by dsimp [L];positivity
  have htc : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have ht₀ : (0:ℝ)<T₀.card := by exact_mod_cast hT₀.card_pos
  have hut : (0:ℝ)<UT.card := by exact_mod_cast (hT.card_pos.trans_le (Finset.card_le_card hTU))
  have hut₀ : (0:ℝ)<UT₀.card := by exact_mod_cast (hT₀.card_pos.trans_le (Finset.card_le_card hsub))
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp := restriction_product_loss (Nat.card K) n T.card S.card T₀.card b L
    (finrank K V) (finrank K U) hq hL (Submodule.finrank_le U) horig (by
      simpa only [M,Nat.cast_pow] using hprod)
  refine ⟨k,hk,hT₀,hsub,hp,fun p hp=>restricted_degree_bound U S T _ k hp,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (reduced_incidence_bound U S T (Real.sqrt τ/Nat.card K) k) hq.le
    calc
      _  ≤  (Nat.card K:ℝ)*(Real.sqrt τ/Nat.card K*S.card*T₀.card) := hh
      _ = _ := by field_simp;ring
  · exact logarithmic_gap_of_cross hut₀ ht₀ hut htc (by positivity : (0:ℝ)<4*L) hgap
  · intro u v hu huv
    apply logarithmic_gap_of_cross hu hs (hu.trans_le huv) hn (by norm_num : (0:ℝ)<100)
    have hh := mul_le_mul_of_nonneg_left hsize hu.le
    have hh' := mul_le_mul_of_nonneg_right huv (by positivity : (0:ℝ) ≤ 100*S.card)
    nlinarith only [hh,hh']

end SharpRamseyFive.ProjectiveRestriction

end OAI
