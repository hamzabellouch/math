import OAI.GroupTheory.Kervaire.Realization

namespace OAI

section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def annulus (ρ : Perm I) : Perm (I ⊕ I) := ρ.symm.sumCongr ρ
def pairing : Perm (I ⊕ I) := Equiv.sumComm I I

omit [DecidableEq I] in
lemma annulus_planar (ρ : Perm I) (hc : ∀ i j, ρ.SameCycle i j) : planar (annulus ρ) pairing := by
  have hn : numCycles ρ = 1 := by
    have hh := numCycles_eq_card ρ (fun _ : I ↦ (PUnit.unit : (PUnit : Type)))
      (fun _ ↦ ⟨Classical.arbitrary I,rfl⟩) (fun x y ↦ ⟨fun _ ↦ rfl,fun _ ↦ hc x y⟩)
    simpa only [Fintype.card_punit] using hh
  have hv : numCycles (annulus ρ) = 2 := by
    rw [annulus,numCycles_sumPerm,← Equiv.Perm.inv_def,numCycles_inverse,hn]
  have ht : ∀ d : I ⊕ I, pairing (pairing d) = d := by rintro (d|d) <;> rfl
  have he : ∀ d : I ⊕ I, pairing d ≠ d := by rintro (d|d) <;> simp [pairing]
  have hf : ∀ d : I ⊕ I, ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) (((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) d) = d := by
    rintro (d|d) <;> simp [annulus,pairing]
  have hg : ∀ d : I ⊕ I, ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) d ≠ d := by rintro (d|d) <;> simp [annulus,pairing]
  have hnt := numCycles_involution pairing ht he
  have hnf := numCycles_involution ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) hf hg
  have hcc : components (annulus ρ) pairing = ⊤ := by
    apply top_unique
    intro x y _
    have hh (i j : I) : (annulus ρ).SameCycle (Sum.inr i) (Sum.inr j) := by
      rw [annulus,sameCycle_sumPerm]
      exact congrArg Sum.inr (Quotient.sound (s := SameCycle.setoid ρ) (hc i j))
    have hi (i : I) : components (annulus ρ) pairing (Sum.inl i) (Sum.inr i) :=
      (le_sup_right : SameCycle.setoid pairing ≤ components (annulus ρ) pairing) SameCycle.rfl.apply_right
    have hj (i j : I) : components (annulus ρ) pairing (Sum.inr i) (Sum.inr j) :=
      (le_sup_left : SameCycle.setoid (annulus ρ) ≤ components (annulus ρ) pairing) (hh i j)
    cases x with
    | inl i =>
      cases y with
      | inl j => exact (components _ _).trans' (hi i) ((components _ _).trans' (hj i j) ((components _ _).symm' (hi j)))
      | inr j => exact (components _ _).trans' (hi i) (hj i j)
    | inr i =>
      cases y with
      | inl j => exact (components _ _).trans' (hj i j) ((components _ _).symm' (hi j))
      | inr j => exact hj i j
  unfold planar
  rw [hv,hcc,classes_top]
  simp only [Fintype.card_sum] at hnt hnf ⊢
  omega

/-- Adding a zero-sign marked corner just inserts a bivalent boundary point. -/
def markAnnulus (ρ : Perm I) (i : I) : Perm ((I ⊕ I) ⊕ (PUnit : Type)) :=
  swap (Sum.inl (Sum.inr i)) (Sum.inr PUnit.unit) * ((annulus ρ).sumCongr 1)

omit [Fintype I] [Nonempty I] in
lemma markAnnulus_marker (ρ : Perm I) (i : I) : markAnnulus ρ i (Sum.inr PUnit.unit) = Sum.inl (Sum.inr i) := by
  simp [markAnnulus]
omit [Fintype I] [Nonempty I] in
lemma markAnnulus_disk (ρ : Perm I) (i j : I) : markAnnulus ρ i (Sum.inl (Sum.inl j)) = Sum.inl (Sum.inl (ρ.symm j)) := by
  simp [markAnnulus,annulus,swap_apply_def]
omit [Fintype I] [Nonempty I] in
lemma markAnnulus_outside (ρ : Perm I) (i j : I) : markAnnulus ρ i (Sum.inl (Sum.inr j)) =
    if ρ j = i then Sum.inr PUnit.unit else Sum.inl (Sum.inr (ρ j)) := by
  simp only [markAnnulus,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl,annulus,Sum.map_inr]
  by_cases h : ρ j = i
  · simp only [h,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using h) (by simp),ite_eq_right h]

lemma markAnnulus_planar (ρ : Perm I) (hc : ∀ i j, ρ.SameCycle i j) (i : I) :
    planar (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type))) := by
  apply planar_vertex_join
  · rw [components_sumPerm]
    change ¬ Sum.inl _ = Sum.inr _
    simp
  · exact planar_sumPerm _ _ _ _ (annulus_planar ρ hc) (planar_one_right 1)

omit [Fintype I] [Nonempty I] in
lemma markAnnulus_circle (ρ : Perm I) (i : I) (l : List I) (hc : Circle ρ i l) (hn : i ∉ l) :
    Circle (markAnnulus ρ i) (Sum.inr PUnit.unit) ((i::l).map (fun j ↦ Sum.inl (Sum.inr j))) := by
  have hh := chain_redirect ρ (markAnnulus ρ i) (fun j ↦ Sum.inl (Sum.inr j)) i (Sum.inr PUnit.unit)
    i l hc hn (fun j _ ↦ markAnnulus_outside ρ i j)
  apply List.isChain_cons_cons.mpr
  exact ⟨markAnnulus_marker _ _,by simpa only [List.map_cons,List.cons_append,List.append_eq] using hh⟩
end KervaireRibbon

end

section
namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

def basePotential (ρ : Perm I) (a : I → A) (i : I) : ((I ⊕ I) ⊕ (PUnit : Type)) → A :=
  Sum.elim (Sum.elim (fun _ ↦ 1) (fun j ↦ (a (ρ.symm j))⁻¹)) (fun _ ↦ (a (ρ.symm i))⁻¹)
def baseSign (s : I → ℤ) : ((I ⊕ I) ⊕ (PUnit : Type)) → ℤ :=
  Sum.elim (Sum.elim (fun j ↦ -s j) s) (fun _ ↦ 0)

omit [Fintype I] [Nonempty I] in
lemma base_corner_disk (ρ : Perm I) (a : I → A) (i j : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inl j)) =
      (a (ρ.symm j))⁻¹ := by
  simp [corner,markAnnulus_disk,pairing,basePotential]
omit [Fintype I] [Nonempty I] in
lemma base_corner_outside (ρ : Perm I) (a : I → A) (i j : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inr j)) = a j := by
  unfold corner
  rw [markAnnulus_outside]
  by_cases h : ρ j = i
  · rw [ite_eq_left h]
    have hh : ρ.symm i = j := by rw [← h,ρ.symm_apply_apply]
    simp [pairing,basePotential,hh]
  · rw [ite_eq_right h]
    simp [pairing,basePotential]
omit [Fintype I] [Nonempty I] in
lemma base_corner_marker (ρ : Perm I) (a : I → A) (i : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inr PUnit.unit) = 1 := by
  simp [corner,markAnnulus_marker,basePotential]

/-- The annulus between a single oppositely oriented relator disk and its outside
word has a literal genus-zero ribbon witness. -/
def OuterRibbon.base (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    OuterRibbon (D := (I⊕I)⊕(PUnit : Type)) (V := (PUnit : Type)) ρ a s (Sum.inr PUnit.unit) ((i::l).map (fun j ↦ Sum.inl (Sum.inr j))) := by
  let σ := markAnnulus ρ i
  let θ : Perm ((I ⊕ I) ⊕ (PUnit : Type)) := pairing.sumCongr 1
  let b : DiskAtlas (V := (PUnit : Type)) ρ a s σ (baseSign s) := {
    disk := ⟨fun vi ↦ Sum.inl (Sum.inl vi.2),by
      rintro ⟨v,i⟩ ⟨w,j⟩ he
      have hi := Sum.inl.inj (Sum.inl.inj he)
      cases v; cases w; cases hi; rfl⟩
    ε := fun _ ↦ -1
    polarity := fun _ ↦ Or.inr rfl
    next := by
      intro v j
      change markAnnulus ρ i (Sum.inl (Sum.inl j)) =
        Sum.inl (Sum.inl (if (-1:ℤ)=1 then ρ j else ρ.symm j))
      simpa only [show (-1:ℤ) ≠ 1 by omega,ite_false] using markAnnulus_disk ρ i j
    sign := by intro v j; change -s j = (-1)*s j; exact (neg_one_mul _).symm }
  refine {
    σ := σ, θ := θ, t := baseSign s, u := basePotential ρ a i, atlas := b
    involutive := ?_, planar' := markAnnulus_planar ρ hρ i
    opposite := ?_, marker := rfl, marker_sign := rfl
    circle := markAnnulus_circle ρ i l hc (List.nodup_cons.mp hn).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro ((j|j)|j) <;> rfl
  · rintro ((j|j)|j) <;> simp [θ,pairing,baseSign]
  · apply List.nodup_cons.mpr
    refine ⟨by simp [List.mem_map],hn.map ?_⟩
    intro x y h
    exact Sum.inr.inj (Sum.inl.inj h)
  · intro d hd
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
    exact hs j
  · rintro ⟨v,j⟩
    change Sum.inl (Sum.inl j) ∉ Sum.inr PUnit.unit :: (i::l).map (fun j ↦ Sum.inl (Sum.inr j))
    simp [List.mem_map]
  · rintro ((j|j)|j)
    · exact Or.inl ⟨(PUnit.unit,j),rfl⟩
    · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,hcover j,rfl⟩)))
    · cases j; exact Or.inr (Or.inl (by simp))
  · intro v j
    change vertexCorner ρ a (fun _ : PUnit ↦ -1) (v,j) =
      corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inl j))
    simpa [vertexCorner] using (base_corner_disk ρ a i j).symm

lemma OuterRibbon.value_base (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    (OuterRibbon.base ρ hρ a s hs i l hc hn hcover).value = dartEval s a (i::l) := by
  change dartEval (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i))
    (Sum.inr PUnit.unit :: (i::l).map (fun j ↦ Sum.inl (Sum.inr j))) = _
  rw [dartEval_cons]
  have hm : dartLetter (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i)) (Sum.inr PUnit.unit) = 1 := by
    simp [dartLetter,baseSign,base_corner_marker]
  rw [hm,one_mul]
  unfold dartEval
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply,dartLetter,base_corner_outside,baseSign,Sum.elim_inl,Sum.elim_inr]
end KervaireRibbon

end

end OAI
