import OAI.Analysis.Littlewood.DependentMoments

namespace OAI

universe uI uK uV uJ

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
open Nibble
section SlotGraph
variable {I : Type uI} {K : Type uK} {V : Type uV} [Fintype I] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

def slotVertices (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset (I × K) :=
  Finset.univ.filter (fun v ↦ hit v.1 v.2)

def slotEdges (g : I → V →ₗ[K] K) (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset V :=
  Finset.univ.filter (fun y ↦ ∀ i, hit i (g i y))

def slotSupport (g : I → V →ₗ[K] K) (y : V) : Finset (I × K) :=
  Finset.univ.image (fun i ↦ (i,g i y))

omit [Fintype K] [Fintype V] [DecidableEq V] in
@[simp] lemma mem_slotSupport (g : I → V →ₗ[K] K) (y : V) (i : I) (t : K) :
    (i,t)∈slotSupport g y ↔ g i y=t := by
  simp [slotSupport,Prod.ext_iff]

omit [Fintype K] [Fintype V] [DecidableEq V] in
lemma slotSupport_card (g : I → V →ₗ[K] K) (y : V) :
    (slotSupport g y).card=Fintype.card I := by
  rw [slotSupport,Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro i j h; exact congrArg Prod.fst h

omit [DecidableEq V] in
lemma slotSupport_subset (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] {y : V} (hy : y∈slotEdges g hit) :
    slotSupport g y⊆slotVertices hit := by
  intro v hv
  rcases v with ⟨i,t⟩
  obtain rfl := mem_slotSupport g y i t |>.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2 i⟩

omit [DecidableEq I] [Field K] [DecidableEq K] in
lemma slotVertices_card (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] :
    (slotVertices hit).card=∑ i, (Finset.univ.filter (hit i)).card := by
  classical
  simp only [slotVertices,Finset.card_filter,Fintype.sum_prod_type]

omit [Fintype K] [DecidableEq V] in
lemma slot_degree_fiber (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) (hs : hit i s) :
    incident (slotEdges g hit) (slotSupport g) (i,s)=
      (fiber (g i) s).filter (fun y ↦ ∀ j : {j : I // j≠i}, hit j (g j y)) := by
  classical
  apply Finset.ext
  intro y
  simp only [mem_incident,slotEdges,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_slotSupport,mem_fiber]
  constructor
  · rintro ⟨hy,hys⟩; exact ⟨hys,fun j ↦ hy j⟩
  · rintro ⟨hys,hy⟩
    refine ⟨?_,hys⟩
    intro j
    by_cases hj : j=i
    · subst j; simpa [hys] using hs
    · exact hy ⟨j,hj⟩

omit [Fintype K] in
lemma slot_codegree_subset (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i j : I) (s t : K) :
    incident (slotEdges g hit) (slotSupport g) (i,s) ∩
      incident (slotEdges g hit) (slotSupport g) (j,t) ⊆
        (fiber (g i) s).filter (fun y ↦ g j y=t) := by
  intro y hy
  obtain ⟨hyi,hyj⟩ := Finset.mem_inter.mp hy
  exact Finset.mem_filter.mpr ⟨mem_fiber.mpr (mem_slotSupport _ _ _ _ |>.mp
    (mem_incident _ _ _ _ |>.mp hyi).2),mem_slotSupport _ _ _ _ |>.mp
    (mem_incident _ _ _ _ |>.mp hyj).2⟩

omit [Fintype K] [DecidableEq V] in
lemma slot_same_row_disjoint (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) {s t : K} (hst : s≠t) :
    Disjoint (incident (slotEdges g hit) (slotSupport g) (i,s))
      (incident (slotEdges g hit) (slotSupport g) (i,t)) := by
  apply Finset.disjoint_left.mpr
  intro y hys hyt
  exact hst ((mem_slotSupport _ _ _ _ |>.mp (mem_incident _ _ _ _ |>.mp hys).2).symm.trans
    (mem_slotSupport _ _ _ _ |>.mp (mem_incident _ _ _ _ |>.mp hyt).2))

lemma slot_codegree (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)]
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j)))
    (v w : I × K) (hvw : v≠w) :
    ((incident (slotEdges g hit) (slotSupport g) v ∩
      incident (slotEdges g hit) (slotSupport g) w).card : ℝ) ≤
        Fintype.card V/(Fintype.card K : ℝ)^2 := by
  rcases v with ⟨i,s⟩
  rcases w with ⟨j,t⟩
  by_cases hij : i=j
  · subst j
    have hst : s≠t := fun h ↦ hvw (Prod.ext rfl h)
    rw [Finset.disjoint_iff_inter_eq_empty.mp (slot_same_row_disjoint g hit i hst)]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  · have hcard := Finset.card_le_card (slot_codegree_subset g hit i j s t)
    have hcount := conditional_fiber_count (g i) (g j) (hpair i j hij) s t
    have htotal := fiber_card_mul (g i).toAddMonoidHom (hg i) s
    have hq : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
    apply (Nat.cast_le.mpr hcard : (_ : ℝ)≤_).trans_eq
    apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hq))).mpr
    have hc : (Fintype.card K : ℝ)*((fiber (g i) s).filter (fun y ↦ g j y=t)).card=
        (fiber (g i) s).card := by exact_mod_cast hcount
    have ht : (Fintype.card K : ℝ)*(fiber (g i) s).card=Fintype.card V := by exact_mod_cast htotal
    nlinarith

lemma prod_indicator_eq {J : Type uJ} [Fintype J] (P : J → Prop) [DecidablePred P] :
    (∏ j, if P j then (1 : ℝ) else 0) = if ∀ j, P j then 1 else 0 := by
  classical
  by_cases h : ∀ j, P j
  · simp [h]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact ite_eq_right hj

def slotDensity (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) : ℝ :=
  avg (fun y : fiber (g i) s ↦ ∏ j : {j : I // j≠i}, if hit j (g j y) then (1 : ℝ) else 0)

omit [Fintype K] [DecidableEq V] in
lemma slotDensity_eq (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) :
    slotDensity g hit i s=
      (((fiber (g i) s).filter (fun y ↦ ∀ j : {j : I // j≠i}, hit j (g j y))).card : ℝ)/
        (fiber (g i) s).card := by
  classical
  simp only [slotDensity,prod_indicator_eq,avg,Fintype.card_coe]
  rw [Finset.sum_boole, Finset.univ_eq_attach,
    Finset.filter_attach (fun y : V ↦ ∀ j : {j : I // j≠i}, hit j (g j y)),
    Finset.card_map, Finset.card_attach]

omit [DecidableEq V] in
lemma slot_degree_density (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (hg : ∀ i, Function.Surjective (g i))
    (i : I) (s : K) (hs : hit i s) :
    ((incident (slotEdges g hit) (slotSupport g) (i,s)).card : ℝ)=
      (Fintype.card V/(Fintype.card K : ℝ))*slotDensity g hit i s := by
  rw [slot_degree_fiber g hit i s hs,slotDensity_eq]
  have hc : (Fintype.card K : ℝ)*(fiber (g i) s).card = Fintype.card V :=
    by exact_mod_cast (fiber_card_mul (g i).toAddMonoidHom (hg i) s)
  have hF : (0 : ℝ)<(fiber (g i) s).card := by
    exact_mod_cast (fiber_nonempty (g i).toAddMonoidHom (hg i) s).card_pos
  have hq : (0 : ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  rw [← hc,mul_div_cancel_left₀ _ hq.ne']
  exact (mul_div_cancel₀ _ hF.ne').symm

omit [DecidableEq V] in
lemma slot_degree_near (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (hg : ∀ i, Function.Surjective (g i))
    (i : I) (s : K) (hs : hit i s) {p e : ℝ}
    (hne : |slotDensity g hit i s-p|≤e*p) :
    |((incident (slotEdges g hit) (slotSupport g) (i,s)).card : ℝ)-
      (Fintype.card V/(Fintype.card K : ℝ))*p| ≤
        e*((Fintype.card V/(Fintype.card K : ℝ))*p) := by
  rw [slot_degree_density g hit hg i s hs,← mul_sub,abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ))]
  have h := mul_le_mul_of_nonneg_left hne (by positivity : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ))
  nlinarith only [h]

end SlotGraph
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
section RandomMatching
variable {I : Type} [Fintype I] [DecidableEq I]

lemma random_slot_matching (hr : 1≤Fintype.card I) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) (hη₁ : η≤1) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {K V Ω : Type} [Field K] [Fintype K] [DecidableEq K]
      [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [Fintype Ω] [Nonempty Ω],
    ∀ (g : I → V →ₗ[K] K) (hit : I → K → Ω → Prop)
      [∀ i s ω, Decidable (hit i s ω)] (p a b n : ℝ),
      (∀ i, Function.Surjective (g i)) →
      (∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) →
      0<p → 0≤b →
      (∀ i, avg (fun ω ↦ avg (fun s ↦ (slotDensity g (fun j t ↦ hit j t ω) i s-p)^2))≤a) →
      Fintype.card I*Fintype.card K*a/(e*p/2)^2≤b →
      (∀ ω, ((slotVertices (fun i t ↦ hit i t ω)).card : ℝ)=n) →
      T≤(Fintype.card V/(Fintype.card K : ℝ))*p → T≤n-b →
      Fintype.card V/(Fintype.card K : ℝ)^2≤e*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      n*(Fintype.card V/(Fintype.card K : ℝ)^2)≤K₀*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      b*(Fintype.card V/(Fintype.card K : ℝ)^2)≤e*((Fintype.card V/(Fintype.card K : ℝ))*p)/2 →
      ∃ ω, ∃ M⊆slotEdges g (fun i t ↦ hit i t ω),
        (M : Set V).Pairwise (fun y z ↦ Disjoint (slotSupport g y) (slotSupport g z)) ∧
        (1-η)*(n-b)≤Fintype.card I*(M.card : ℝ) := by
  classical
  obtain ⟨e,T,he,hT,hmatch⟩ := matching_after_pruning
    (Fintype.card I) hr hK₀ hη
  refine ⟨e,T,he,hT,?_⟩
  intro K V Ω instK instFK instDK instV instMV instFV instDV instFΩ instNΩ g hit inst p a b n hg hpair hp hb hvar hbad hn hD hsize hCe hcode hsmall
  obtain ⟨ω,hω⟩ := exists_few_bad_centers_averaged
    (fun i s ω ↦ slotDensity g (fun j t ↦ hit j t ω) i s) p
    (show 0<e*p/2 by positivity) hvar
  let U := slotVertices (fun i t ↦ hit i t ω)
  let B := U.filter (fun v ↦ e*p/2≤|slotDensity g (fun j t ↦ hit j t ω) v.1 v.2-p|)
  have hBU : B⊆U := Finset.filter_subset _ _
  have hB : (B.card : ℝ)≤b := by
    apply le_trans _ (hω.trans hbad)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
  have hnB : n-b≤((U\B).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hBU, Nat.cast_sub (Finset.card_le_card hBU)]
    dsimp [U]
    rw [hn ω]
    linarith
  have hC : (0 : ℝ)≤Fintype.card V/(Fintype.card K : ℝ)^2 := by positivity
  obtain ⟨M,hM,hdis,hMsize⟩ := hmatch U B (slotEdges g (fun i t ↦ hit i t ω))
    (slotSupport g) ((Fintype.card V/(Fintype.card K : ℝ))*p)
    (Fintype.card V/(Fintype.card K : ℝ)^2) hBU hD (hsize.trans hnB) hC hCe
    (by simpa only [U,hn ω] using hcode)
    ((mul_le_mul_of_nonneg_right hB hC).trans hsmall)
    (fun y hy ↦ slotSupport_subset g _ hy)
    (fun y _ ↦ slotSupport_card g y) (by
      rintro ⟨i,s⟩ hv
      obtain ⟨hvU,hvB⟩ := Finset.mem_sdiff.mp hv
      have hh : hit i s ω := (Finset.mem_filter.mp hvU).2
      have hne : |slotDensity g (fun j t ↦ hit j t ω) i s-p|<e*p/2 := by
        exact lt_of_not_ge (fun h ↦ hvB (Finset.mem_filter.mpr ⟨hvU,h⟩))
      have h := slot_degree_near g (fun j t ↦ hit j t ω) hg i s hh
        (e := e/2) (p := p) (by nlinarith only [hne])
      convert h using 1 ; ring) (by
      rintro ⟨i,s⟩ _ ⟨j,t⟩ _ hne
      exact slot_codegree g (fun a u ↦ hit a u ω) hg hpair (i,s) (j,t) hne)
  exact ⟨ω,M,hM,hdis,(mul_le_mul_of_nonneg_left hnB (sub_nonneg.mpr hη₁)).trans hMsize⟩
end RandomMatching
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable

lemma concrete_slot_variance {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (i₀ : Fin r) (hK : 0<K)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      3*(2*((r-1 : ℕ)*(q-(catalogSet d R K q).card : ℝ)/q+
          2*((r-1 : ℕ) : ℝ)^2*(shortResidues q (R*periodLength (oddLengths d))).card/q)+
        ((r-1 : ℕ) : ℝ)^2*
          (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ)/q) := by
  have hL := periodLength_pos d i₀
  have : Nonempty (Fin (periodLength (oddLengths d))) := ⟨⟨0,hL⟩⟩
  obtain ⟨chunk,hchunk,hhit,hB,hcollision⟩ := catalog_chunk_system d R K q i₀ hK hq
  have h := averaged_density_variance (g i)
    (fun j : {j : Fin r // j≠i} ↦ g j) (hg i) (fun j ↦ hg j)
    (fun j ↦ hpair i j (Ne.symm j.2))
    (fun j l hjl ↦ hpair j l (fun h ↦ hjl (Subtype.ext h)))
    (catalogSet d R K q) (shortResidues q (R*periodLength (oddLengths d))) chunk hcollision
    (fun j t ω ↦ slotHit d R K q j ω t) (fun j ↦ hhit j)
    (B := (((q-(catalogSet d R K q).card+2*((R-2)*periodLength (oddLengths d))) : ℕ) : ℝ))
    (fun k ↦ by exact_mod_cast hB k)
  have hc : Fintype.card {j : Fin r // j≠i}=r-1 := by
    simp [Fintype.card_subtype_compl]
  convert h using 1 <;>
    simp only [slotDensity, hc, Fintype.card_prod, Fintype.card_fin,Fintype.card_bool,ZMod.card,
      Nat.cast_mul, Nat.cast_ofNat, mul_comm (periodLength (oddLengths d) : ℝ) 2]

lemma concrete_slot_vertices_card {r q : ℕ} [Fact q.Prime] (d : Fin r → ℕ)
    (R K : ℕ) (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (slotVertices (fun i t ↦ slotHit d R K q i ω t)).card=r*K*(R-1) := by
  rw [slotVertices_card]
  simp only [slotHit_card d R K q _ hq ω,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul, Nat.cast_id]
  ring

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI
