import OAI.Combinatorics.MatchingEntropy.Counting

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section SharedEquation
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_shared (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U)
    (l : B →ₗ[ℝ] ℝ) (r : C →ₗ[ℝ] ℝ) (hl : W ≤ l.ker) (hr : Z ≤ r.ker)
    (heq : ∀ u, l (f u) = r (g u)) (b : B) (hb : l b ≠ 0) :
    finrank ℝ (A ⧸ U) + 1 ≤ finrank ℝ (B ⧸ W) + finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  let L : ((B ⧸ W) × (C ⧸ Z)) →ₗ[ℝ] ℝ :=
    (W.liftQ l hl).comp (LinearMap.fst ℝ _ _) -
      (Z.liftQ r hr).comp (LinearMap.snd ℝ _ _)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u)) = 0 := hu
    apply h u
    · simpa using congrArg Prod.fst hh
    · simpa using congrArg Prod.snd hh
  have hL : ∀ u, F u ∈ L.ker := by
    intro u
    change l (f u) - r (g u) = 0
    exact sub_eq_zero.mpr (heq u)
  let F' := F.codRestrict L.ker hL
  have hk' : F'.ker ≤ U := by
    intro u hu
    apply hk
    have hh := congrArg Subtype.val (show F' u = 0 from hu)
    exact hh
  have hdim := quotient_finrank_le_of_ker_le U F' hk'
  have hsum := L.finrank_range_add_finrank_ker
  have hpos : 1 ≤ finrank ℝ L.range := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hh
    have hm : L (W.mkQ b, 0) ∈ L.range := ⟨_, rfl⟩
    rw [hh] at hm
    have hz : L (W.mkQ b, 0) = 0 := hm
    apply hb
    simpa [L] using hz
  rw [Module.finrank_prod] at hsum
  omega
end SharedEquation

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def lowerObjective (c : ℝ) (x : E → ℝ) : ℝ := entropy x - c * complementEntropy x

open LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem positiveExtension_self {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) :
    positiveExtension x (fun e => x e.val) = x := by
  funext e
  by_cases he : 0 < x e
  · simp [positiveExtension, he]
  · simp [positiveExtension, le_antisymm (le_of_not_gt he) (hx e)]

def boundaryLinear (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0 < G.sideMarginal x S e} → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj none).comp
    ((G.onSide S).degreeLinear.comp (positiveExtension (G.sideMarginal x S)))

omit [Fintype V] [DecidableEq E] in
theorem boundaryLinear_restriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0 < x e} → ℝ) :
    boundaryLinear G x S (G.sideRestriction x S u) = G.cutMass (positiveExtension x u) S := by
  change (G.onSide S).degree (fun e => positiveExtension x u e.val) none = _
  exact G.onSide_degree_none S _

omit [Fintype V] [DecidableEq E] in
theorem boundaryLinear_face (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    (G.onSide S).faceSpace (G.sideMarginal x S) ≤ (boundaryLinear G x S).ker := by
  intro u hu
  exact congrFun hu.1 none

theorem faceCodimension_le_sides_shared (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S = 1) :
    G.faceCodimension x + 1 ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  apply quotient_finrank_shared (G.faceSpace x)
    ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)
    (boundaryLinear G x S) (boundaryLinear G x Sᶜ)
    (boundaryLinear_face G x S) (boundaryLinear_face G x Sᶜ)
    (fun u => by simp only [boundaryLinear_restriction, cutMass, cut_compl])
    (fun e => G.sideMarginal x S e.val)
  have hext := positiveExtension_self (x := G.sideMarginal x S) (fun e => hx.1 e.val)
  change (G.onSide S).degree
    (positiveExtension (G.sideMarginal x S) (fun e => G.sideMarginal x S e.val)) none ≠ 0
  rw [hext, G.onSide_degree_none, ht]
  norm_num

omit [Fintype E] [DecidableEq E] in

theorem incident_of_card_two (G : LooplessGraph V E) (hV : Fintype.card V = 2)
    (v : V) (e : E) : G.Incident v e := by
  have hp : ({G.left e, G.right e} : Finset V) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hV, G.loopless e]
  have hv : v ∈ ({G.left e, G.right e} : Finset V) := hp ▸ Finset.mem_univ v
  simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm, Incident] using hv

omit [DecidableEq E] in

theorem faceCodimension_two (G : LooplessGraph V E) (hV : Fintype.card V = 2)
    (x : E → ℝ) : G.faceCodimension x ≤ 1 := by
  classical
  let L : ({e // 0 < x e} → ℝ) →ₗ[ℝ] ℝ :=
    (Finset.univ.sum (fun e : E => LinearMap.proj e)).comp (positiveExtension x)
  have heven : Even (Fintype.card V) := by simp [hV]
  have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3 ≤ S.card ∧ 3 ≤ Sᶜ.card ∧ G.cutMass x S = 1 := by
    rintro ⟨S, _, hlo, _, _⟩
    have hc := Finset.card_le_univ S
    omega
  have hker : L.ker ≤ G.faceSpace x := by
    intro u hu
    have hz : ∑ e, positiveExtension x u e = 0 := by simpa [L] using hu
    have hd : ∀ v, G.degree (positiveExtension x u) v = 0 := by
      intro v
      simpa only [degree, incident_of_card_two G hV v, ite_true] using hz
    refine ⟨funext hd, ?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ hd
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) L hker

theorem sharp_face_rank_aux (n : ℕ) :
    ∀ {W : Type uW} {F : Type uF} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, 2 * (G.faceCodimension x + 2) ≤ 3 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := faceCodimension_le_sides_shared G heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change 2 * ((G.onSide S).faceCodimension (G.sideMarginal x S) + 2) ≤ _ at hb1
      change 2 * ((G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) + 2) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

theorem sharp_face_rank (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ}
    (hx : x ∈ G.polytope) : G.faceCodimension x + 2 ≤ 3 * m := by
  by_cases hm1 : m = 1
  · have htwo : Fintype.card V = 2 := by omega
    have hb := faceCodimension_two G htwo x
    omega
  · have heven : Even (Fintype.card V) := by rw [hV]; exact even_two_mul m
    have hb := sharp_face_rank_aux (Fintype.card V) G rfl heven (by omega) x
      (G.polytope_subset_constraintPolytope hx)
    omega

end MatchingEntropyBounds.Refined

end

end OAI
