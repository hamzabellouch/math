import OAI.NumberTheory.PowerFree.ResidueBounds

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

def treeLevel {σ : Type*} [DecidableEq σ] (root : Finset σ)
    (child : ℕ → σ → Finset σ) : ℕ → Finset σ
  | 0 => root
  | i+1 => (treeLevel root child i).biUnion (child i)

theorem treeLevel_card_le {σ : Type*} [DecidableEq σ] (root : Finset σ)
    (child : ℕ → σ → Finset σ) (B : ℕ → ℕ)
    (hB : ∀ i s, s ∈ treeLevel root child i → (child i s).card ≤ B i) (i : ℕ) :
    (treeLevel root child i).card ≤ root.card * ∏ j ∈ Finset.range i, B j := by
  induction i with
  | zero => simp [treeLevel]
  | succ i ih =>
    calc
      _ ≤ ∑ s ∈ treeLevel root child i, (child i s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ treeLevel root child i, B i := Finset.sum_le_sum (hB i)
      _ = (treeLevel root child i).card * B i := by simp
      _ ≤ (root.card * ∏ j ∈ Finset.range i, B j)*B i := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [Finset.prod_range_succ,mul_assoc]

theorem cardinal_tree_stopping {σ α : Type*} [DecidableEq σ] [DecidableEq α]
    (S : Finset α) (root : Finset σ) (child : ℕ → σ → Finset σ)
    (B : ℕ → ℕ) (r L : ℕ) (depth : α → ℕ) (node : α → σ)
    (hB : ∀ i s, s ∈ treeLevel root child i → (child i s).card ≤ B i)
    (hB1 : ∀ i, 1 ≤ B i)
    (hdepth : ∀ z ∈ S, depth z ≤ r)
    (hnode : ∀ z ∈ S, node z ∈ treeLevel root child (depth z))
    (hfiber : ∀ i ≤ r, ∀ s ∈ treeLevel root child i,
      (S.filter fun z => depth z = i ∧ node z = s).card ≤ L) :
    S.card ≤ (r+1)*root.card*(∏ j ∈ Finset.range r, B j)*L := by
  classical
  let T := (Finset.range (r+1)).sigma fun i => treeLevel root child i
  let f : α → Σ _i : ℕ, σ := fun z => ⟨depth z,node z⟩
  have hf : ∀ z ∈ S, f z ∈ T := by
    intro z hz
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by change depth z < r+1; have := hdepth z hz; omega),hnode z hz⟩
  have hprefix (i : ℕ) (hi : i ≤ r) :
      (treeLevel root child i).card ≤ root.card*∏ j ∈ Finset.range r, B j := by
    refine (treeLevel_card_le root child B hB i).trans (Nat.mul_le_mul_left _ ?_)
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hi)
    intro j _ _
    exact hB1 j
  calc
    S.card = ∑ t ∈ T, (S.filter fun z => f z = t).card := Finset.card_eq_sum_card_fiberwise hf
    _ ≤ ∑ _t ∈ T, L := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨hi,hs⟩ := Finset.mem_sigma.mp ht
      have hir : t.1 ≤ r := by have := Finset.mem_range.mp hi; omega
      rcases t with ⟨i,s⟩
      simpa [f] using hfiber i hir s hs
    _ = T.card*L := by simp
    _ ≤ ((r+1)*(root.card*∏ j ∈ Finset.range r, B j))*L := by
      apply Nat.mul_le_mul_right
      rw [Finset.card_sigma]
      calc
        _ ≤ ∑ _i ∈ Finset.range (r+1), root.card*∏ j ∈ Finset.range r, B j := by
          apply Finset.sum_le_sum
          intro i hi
          exact hprefix i (by have := Finset.mem_range.mp hi; omega)
        _ = _ := by simp
    _ = _ := by ring

open MvPolynomial
open scoped BigOperators

theorem physical_initial_states {n : ℕ} (G : KernelGeometry n) (A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (hG : ∀ z ∈ G.points, PointOn I z) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h e ∧
    ∃ start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n,
      ∀ z, start z ∈ L ∧ PhysicalState G h (patchDegreeBudget n A h e) z.val (start z) := by
  classical
  obtain ⟨L,hL,hgood,hcover⟩ := bounded_integer_patch_cover A h e I hd he G.points hG
    G.height G.one_le_height G.bounded
  choose start hstart hcov using fun z : G.points => hcover z.val z.property
  refine ⟨L,hL,start,fun z => ⟨hstart z,?_⟩⟩
  have hs := hgood (start z) (hstart z)
  exact ⟨⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hcov z⟩

theorem card_nonsingular_roots_indexed {κ β K : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
    [Field K] (D : ℕ) (f : κ → MvPolynomial κ K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : β → κ → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card β ≤ (D+1)^Fintype.card κ := by
  classical
  let e := Fintype.equivFin κ
  let f' : Fin (Fintype.card κ) → MvPolynomial (Fin (Fintype.card κ)) K :=
    fun i => rename e (f (e.symm i))
  let a' : β → Fin (Fintype.card κ) → K := fun b i => a b (e.symm i)
  have hev (b : β) (p : MvPolynomial κ K) : eval (a' b) (rename e p) = eval (a b) p := by
    rw [eval_rename]
    simp [a',Function.comp_def]
  apply card_nonsingular_polynomial_roots D f'
    (fun i => (totalDegree_rename_le e _).trans (hf (e.symm i))) a'
  · intro b c hab
    apply hinj
    funext j
    simpa [a'] using congrFun hab (e j)
  · intro b i
    exact (hev b _).trans (ha b (e.symm i))
  · intro b
    have heq : (Matrix.of (fun i j => eval (a' b) (pderiv j (f' i)))) =
        Matrix.reindex e e (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))) := by
      ext i j
      change eval (a' b) (pderiv j (rename e (f (e.symm i)))) = _
      rw [← e.apply_symm_apply j, pderiv_rename e.injective, hev]
      simp [Matrix.reindex,Matrix.of_apply]
    rw [heq,Matrix.det_reindex_self]
    exact hJ b

theorem card_smooth_patch_indexed {ι κ β K : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [Fintype β] [Field K] [Fintype K]
    (D : ℕ) (G : κ → MvPolynomial (ι ⊕ κ) K)
    (hG : ∀ j, (G j).totalDegree ≤ D) (z : β → (ι ⊕ κ) → K)
    (hinj : Function.Injective z) (hz : ∀ b j, eval (z b) (G j) = 0)
    (hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0) :
    Fintype.card β ≤ Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by
  classical
  let free : β → ι → K := fun b i => z b (Sum.inl i)
  have hfiber (x : ι → K) : Fintype.card {b // free b = x} ≤ (D+1)^Fintype.card κ := by
    let a : {b // free b = x} → κ → K := fun b j => z b.val (Sum.inr j)
    have heq (b : {b // free b = x}) : Sum.elim x (a b) = z b.val := by
      funext j
      cases j with
      | inl i => exact (congrFun b.property i).symm
      | inr j => rfl
    apply card_nonsingular_roots_indexed D (fun j => partialEval x (G j))
      (fun j => (totalDegree_partialEval_le x (G j)).trans (hG j)) a
    · intro b b' h
      apply Subtype.ext
      apply hinj
      rw [← heq b, ← heq b',h]
    · intro b j
      rw [eval_partialEval,heq]
      exact hz b.val j
    · intro b
      simpa only [pderiv_partialEval,eval_partialEval,heq] using hminor b.val
  calc
    Fintype.card β = ∑ x : ι → K, Fintype.card {b // free b = x} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv free)).symm
    _ ≤ ∑ _x : ι → K, (D+1)^Fintype.card κ := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by simp

noncomputable def IntegerPatch.goodResidues {n : ℕ} (P : IntegerPatch n)
    (K : Type*) [Field K] [Fintype K] : Finset (Fin n → K) := by
  classical
  exact Finset.univ.filter fun x =>
    (∀ i, eval x (MvPolynomial.map (Int.castRingHom K) (P.equations i)) = 0) ∧
    eval x (MvPolynomial.map (Int.castRingHom K) P.minor) ≠ 0

theorem IntegerPatch.card_goodResidues {n : ℕ} (P : IntegerPatch n)
    (K : Type*) [Field K] [Fintype K] (D : ℕ)
    (hD : ∀ i, (P.equations i).totalDegree ≤ D) :
    (P.goodResidues K).card ≤ Fintype.card K ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) := by
  classical
  let e := Equiv.Set.sumCompl P.free
  let G : ↥(P.freeᶜ) → MvPolynomial (P.free ⊕ ↥(P.freeᶜ)) K :=
    fun i => rename e.symm (MvPolynomial.map (Int.castRingHom K) (P.equations i))
  let z : P.goodResidues K → (P.free ⊕ ↥(P.freeᶜ)) → K :=
    fun b j => b.val (e j)
  have hev (b : P.goodResidues K) (p : MvPolynomial (Fin n) K) :
      eval (z b) (rename e.symm p) = eval b.val p := by
    rw [eval_rename]
    simp [z,Function.comp_def]
  have heq (i : ↥(P.freeᶜ)) : e.symm i.val = Sum.inr i := by
    apply e.injective
    simp [e]
  have hcard := card_smooth_patch_indexed D G (fun i =>
    (totalDegree_rename_le e.symm _).trans
      ((Finset.sup_mono (support_map_subset _ _)).trans (hD i))) z
  have hz : Function.Injective z := by
    intro b c h
    apply Subtype.ext
    funext j
    simpa [z] using congrFun h (e.symm j)
  have hroot : ∀ b i, eval (z b) (G i) = 0 := by
    intro b i
    exact (hev b _).trans ((Finset.mem_filter.mp b.property).2.1 i)
  have hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0 := by
    intro b
    have heval : (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))) =
        (Matrix.of (fun i j => eval b.val (pderiv j.val
          (MvPolynomial.map (Int.castRingHom K) (P.equations i))))) := by
      ext i j
      change eval (z b) (pderiv (Sum.inr j) (rename e.symm _)) = _
      rw [← heq j,pderiv_rename e.symm.injective,hev]
      rfl
    rw [heval]
    have hb := (Finset.mem_filter.mp b.property).2.2
    rw [map_integer_minor] at hb
    have hd := (eval b.val).map_det (fun i j : ↥(P.freeᶜ) =>
      pderiv j.val (MvPolynomial.map (Int.castRingHom K) (P.equations i)))
    exact fun hz => hb (hd.trans hz)
  simpa only [Fintype.card_coe,Nat.card_eq_fintype_card] using hcard hz hroot hminor

attribute [local instance] Classical.propDecidable

def residueTuple {n : ℕ} (Q : Finset ℕ) (z : Fin n → ℤ) :
    ∀ p : Q, Fin n → ZMod p.val := fun p i => (z i : ZMod p.val)

theorem residueTuple_eq_iff {n : ℕ} (Q : Finset ℕ) (z w : Fin n → ℤ) :
    residueTuple Q z = residueTuple Q w ↔ ∀ p ∈ Q, ∀ i, (p : ℤ) ∣ w i-z i := by
  constructor
  · intro h p hp i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h ⟨p,hp⟩) i).symm
  · intro h
    funext p i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (w i-z i) p.val).mpr (h p.val p.property i)
    rw [Int.cast_sub,sub_eq_zero] at hz
    exact hz.symm

theorem IntegerPatch.eval_equation_zero {n : ℕ} {P : IntegerPatch n}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.On I) {z : Fin n → ℤ}
    (hz : PointOn I z) (j : ↥(P.freeᶜ)) : eval z (P.equations j) = 0 := by
  have h := hz _ (hP.2.1 j)
  rw [eval_int_map] at h
  exact_mod_cast h

theorem IntegerPatch.residue_mem_iff {n p : ℕ} (P : IntegerPatch n) [Fact p.Prime]
    (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0) :
    (fun i => (z i : ZMod p)) ∈ P.goodResidues (ZMod p) ↔ ¬ (p : ℤ) ∣ eval z P.minor := by
  classical
  simp only [IntegerPatch.goodResidues,Finset.mem_filter,Finset.mem_univ,true_and,eval_int_map,hz,Int.cast_zero,implies_true,true_and]
  exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ p)

theorem card_filter_coe_finset {α : Type*} (Q : Finset α) (p : α → Prop) :
    (Finset.univ.filter fun a : Q => p a.val).card = (Q.filter p).card := by
  classical
  rw [Finset.card_filter,Finset.card_filter]
  exact Finset.sum_coe_sort Q (fun a => if p a then (1 : ℕ) else 0)

theorem IntegerPatch.card_bad_residue_tuple {n : ℕ} (P : IntegerPatch n)
    (Q : Finset ℕ) [∀ p : Q, Fact p.val.Prime] (z : Fin n → ℤ)
    (hz : ∀ j, eval z (P.equations j) = 0) :
    (Finset.univ.filter fun p : Q => residueTuple Q z p ∉ P.goodResidues (ZMod p.val)).card =
      (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card := by
  classical
  have heq : (Finset.univ.filter fun p : Q => residueTuple Q z p ∉ P.goodResidues (ZMod p.val)) =
      Finset.univ.filter fun p : Q => (p.val : ℤ) ∣ eval z P.minor := by
    apply Finset.filter_congr
    intro p _
    change ¬ ((fun i => (z i : ZMod p.val)) ∈ P.goodResidues (ZMod p.val)) ↔ _
    rw [P.residue_mem_iff z hz,not_not]
  rw [heq]
  convert card_filter_coe_finset Q (fun p : ℕ => (p : ℤ) ∣ eval z P.minor) using 1 <;> congr 1 <;> ext p <;> simp

theorem IntegerPatch.card_goodResidues_zmod_le {n p : ℕ} (P : IntegerPatch n) [Fact p.Prime]
    (D h M : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D) (hupper : p ≤ M) :
    (P.goodResidues (ZMod p)).card ≤ (D+1)^n * M^h := by
  classical
  refine (P.card_goodResidues (ZMod p) D hD).trans ?_
  rw [ZMod.card]
  have hc : Nat.card ↥(P.freeᶜ) ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => i ∈ P.freeᶜ)
  calc
    p ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) ≤ M^h*(D+1)^n := by
      apply Nat.mul_le_mul
      · exact (Nat.pow_le_pow_left hupper _).trans (Nat.pow_le_pow_right hM hfree)
      · exact Nat.pow_le_pow_right (by omega) hc
    _ = _ := by ring

theorem IntegerPatch.card_residue_image {n : ℕ} (P : IntegerPatch n)
    (D h M b : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime) (hupper : ∀ p ∈ Q, p ≤ M)
    (S : Finset (Fin n → ℤ)) (hroot : ∀ z ∈ S, ∀ j, eval z (P.equations j) = 0)
    (hbad : ∀ z ∈ S, (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card ≤ b) :
    (S.image (residueTuple Q)).card ≤
      2^Q.card * ((D+1)^n)^Q.card * M^(h*Q.card+n*b) := by
  classical
  let (p : Q) : Fact p.val.Prime := ⟨hprime p.val p.property⟩
  let good (p : Q) : Finset (Fin n → ZMod p.val) := P.goodResidues (ZMod p.val)
  have hall (p : Q) : Fintype.card (Fin n → ZMod p.val) ≤ M^n := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]
    exact Nat.pow_le_pow_left (hupper p.val p.property) n
  have hgood (p : Q) : (good p).card ≤ (D+1)^n * M^h :=
    P.card_goodResidues_zmod_le D h M hM hfree hD (hupper p.val p.property)
  let R : Finset (∀ p : Q, Fin n → ZMod p.val) := Finset.univ.filter fun x =>
    (Finset.univ.filter fun p => x p ∉ good p).card ≤ b
  have hsub : S.image (residueTuple Q) ⊆ R := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (P.card_bad_residue_tuple Q z (hroot z hz)).le.trans (hbad z hz)
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Fintype.card_coe] using
      card_regular_residue_tuples good ((D+1)^n) M h n b (one_le_pow₀ (by omega)) hM hall hgood)

end QuarticPowerFree

end OAI
