import OAI.Combinatorics.CycleDecomposition.BatchPreparation

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma family_quotient_image_order {V I : Type} [Fintype V] [Fintype I]
    (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : ∀ i, PairingSpace (X i)) (W : Finset V) (hX : ∀ i, X i ⊆ W) :
    (W.image (familyProject X hd p)).card + ∑ i, (X i).card / 2 = W.card := by
  classical
  let projMap := familyProject X hd p
  have hi : Set.InjOn projMap (↑Wᶜ : Set V) := by
    intro x hx y hy h
    rcases (familyProject_eq_iff X hd p x y).mp h with he | ⟨i,hx',hy',_⟩
    · exact he
    · exact False.elim (Finset.mem_compl.mp hx (hX i hx'))
  have hd' : Disjoint (W.image projMap) (Wᶜ.image projMap) := by
    apply Finset.disjoint_left.mpr
    rintro z hz hz'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hz'
    rcases (familyProject_eq_iff X hd p y x).mp he with he | ⟨i,hy',hx',_⟩
    · subst y; exact Finset.mem_compl.mp hy hx
    · exact Finset.mem_compl.mp hy (hX i hy')
  have hu : W.image projMap ∪ Wᶜ.image projMap = univ := by
    rw [← Finset.image_union,Finset.union_compl]
    exact Finset.image_univ_of_surjective (familyProject_surjective X hd p)
  have hc := Finset.card_union_of_disjoint hd'
  rw [hu,Finset.card_univ,Finset.card_image_of_injOn hi] at hc
  have hc' := Finset.card_compl W
  have h := family_quotient_order_add X hd p
  dsimp only [projMap] at hc
  have hWcard := Finset.card_le_univ W
  omega

lemma PreparedBatch.quotient_supported {V I : Type} [Fintype V] [Fintype I]
    {G : SimpleGraph V} {X : I → Finset V} {hd}
    (b : PreparedBatch G X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, G.Adj x y → x ∈ W ∧ y ∈ W) :
    ∀ ⦃x y⦄, b.quotient.Adj x y →
      x ∈ W.image (familyProject X hd b.pairing) ∧
      y ∈ W.image (familyProject X hd b.pairing) := by
  classical
  intro x y hxy
  have he : s(x,y) ∈ b.quotient.edgeSet := hxy
  rw [b.quotient_edges] at he
  obtain ⟨e,he,heq⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := b.retained_subset he
    have hu := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).1
    have hv := Finset.mem_image_of_mem (familyProject X hd b.pairing) (hW huv).2
    change s(familyProject X hd b.pairing u,familyProject X hd b.pairing v) = s(x,y) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hu,hv⟩
    · exact ⟨hv,hu⟩

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

lemma deleted_boundary_card_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges U Uᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ F.card := by
  apply Finset.card_le_card_of_injOn (fun e : V × V => s(e.1, e.2))
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · exact (boundary_sym2_injective P U).mono (by
      intro e he
      exact (Finset.mem_filter.mp he).1)

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

theorem routing_union_growth_step
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (F.card : ℝ) ≤ h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  apply routing_union_growth_step_of_boundary P h hexp hr F B Bnext W hmono hsmall
  · have hd : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤ F.card := by
      exact_mod_cast deleted_boundary_card_le P B F
    exact hd.trans hF
  · exact hW
  · exact hextend

def avoidGraph (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    SimpleGraph V where
  Adj v w := P.Adj v w ∧ s(v, w) ∉ F ∧ v ∉ W ∧ w ∉ W
  symm := ⟨by
    intro v w h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2.1, h.2.2.2, h.2.2.1⟩⟩
  loopless := ⟨by intro v h; exact P.irrefl h.1⟩

noncomputable def walkBall (G : SimpleGraph V) (s : V) (t : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : G.Walk s v, p.length ≤ t)

@[simp] lemma mem_walkBall {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (s v : V) (t : ℕ) :
    v ∈ walkBall G s t ↔ ∃ p : G.Walk s v, p.length ≤ t := by
  classical
  simp [walkBall]

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

noncomputable def rootBallUnion (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t : ℕ) : Finset V :=
  A.biUnion (fun s => walkBall (avoidGraph P F (W s)) s t)

lemma rootBallUnion_mono_time (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) {t u : ℕ} (htu : t ≤ u) :
    rootBallUnion P F W A t ⊆ rootBallUnion P F W A u :=
  Finset.biUnion_mono (fun s _ => walkBall_mono _ s htu)

lemma roots_subset_rootBallUnion (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t : ℕ) : A ⊆ rootBallUnion P F W A t := by
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨s, hs, root_mem_walkBall _ _ _⟩

theorem rootBallUnion_growth_step
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (A : Finset V) (t : ℕ)
    (hroots : ∀ s ∈ A, s ∉ W s)
    (hW : ∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4)
    (hsmall : ((rootBallUnion P F W A t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W A t).card / 4) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (rootBallUnion P F W A t).card ≤
      ((rootBallUnion P F W A (t + 1)).card : ℝ) := by
  classical
  let B := rootBallUnion P F W A t
  have hchoose : ∀ v ∈ B, ∃ s ∈ A, v ∈ walkBall (avoidGraph P F (W s)) s t := by
    intro v hv
    exact Finset.mem_biUnion.mp hv
  choose s hsA hreach using hchoose
  let forbid : V → Finset V := fun v => if hv : v ∈ B then W (s v hv) else ∅
  apply routing_union_growth_step P h hexp hr F B (rootBallUnion P F W A (t + 1)) forbid
      (rootBallUnion_mono_time P F W A (Nat.le_succ t)) hsmall hF
  · intro v hv
    simpa only [forbid, dite_eq_left hv] using hW (s v hv) (hsA v hv)
  · intro v hv w _ hadj hdel hforbid
    have hvs : v ∈ walkBall (avoidGraph P F (W (s v hv))) (s v hv) t := hreach v hv
    have hnv : v ∉ W (s v hv) :=
      (Finset.disjoint_left.mp (ball_avoids P F (W (s v hv)) (s v hv)
        (hroots (s v hv) (hsA v hv)) t)) hvs
    have hnw : w ∉ W (s v hv) := by simpa only [forbid, dite_eq_left hv] using hforbid
    exact Finset.mem_biUnion.mpr ⟨s v hv, hsA v hv,
      walkBall_step _ _ v w t hvs ⟨hadj, hdel, hnv, hnw⟩⟩

theorem rootBallUnion_growth_block
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (A : Finset V) (t g : ℕ)
    (hroots : ∀ s ∈ A, s ∉ W s)
    (hW : ∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4)
    (hpos : 1 ≤ (rootBallUnion P F W A t).card)
    (hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W A t).card / 4)
    (hg : (Fintype.card V : ℝ) / 2 < (1 + h / (2 * (Fintype.card V : ℝ))) ^ g) :
    (Fintype.card V : ℝ) / 2 < (rootBallUnion P F W A (t + g)).card := by
  by_contra hnot
  have hend := le_of_not_gt hnot
  let b : ℕ → ℝ := fun j => (rootBallUnion P F W A (t + j)).card
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmono : Monotone b := by
    intro j k hjk
    dsimp [b]
    exact_mod_cast Finset.card_le_card
      (rootBallUnion_mono_time P F W A (Nat.add_le_add_left hjk t))
  have hbase : 1 ≤ b 0 := by dsimp [b]; simpa using (Nat.cast_le (α := ℝ)).mpr hpos
  have hstep : ∀ j < g, c * b j ≤ b (j + 1) := by
    intro j hj
    have hsmall : b j ≤ (Fintype.card V : ℝ) / 2 :=
      (hmono (Nat.le_of_lt hj)).trans hend
    have hFj : (F.card : ℝ) ≤ h * (rootBallUnion P F W A (t + j)).card / 4 := by
      have hbj := hmono (Nat.zero_le j)
      dsimp [b] at hbj
      nlinarith
    simpa only [c, b, Nat.add_assoc] using
      rootBallUnion_growth_step P h hexp hr F W A (t + j) hroots hW hsmall hFj
  have hpow : ∀ j ≤ g, c ^ j ≤ b j := by
    intro j
    induction j with
    | zero => intro _; simpa using hbase
    | succ j ih =>
      intro hjg
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * b j := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ b (j + 1) := hstep j (by omega)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma rootBallUnion_halve (P : SimpleGraph V) (F : Finset (Sym2 V))
    (W : V → Finset V) (A : Finset V) (t k : ℕ) (u : ℝ)
    (hcard : A.card ≤ 2 * k)
    (hlarge : 2 * u < (rootBallUnion P F W A t).card) :
    ∃ A' ⊆ A, A'.card ≤ k ∧ u < (rootBallUnion P F W A' t).card := by
  obtain ⟨A₁, hsub, hcard₁⟩ := Finset.exists_subset_card_eq (min_le_right k A.card)
  let A₂ := A \ A₁
  have hcard₂ : A₂.card ≤ k := by
    dsimp [A₂]
    rw [Finset.card_sdiff_of_subset hsub, hcard₁]
    omega
  have hcover : A₁ ∪ A₂ = A := Finset.union_sdiff_of_subset hsub
  have hcount : (rootBallUnion P F W A t).card ≤
      (rootBallUnion P F W A₁ t).card + (rootBallUnion P F W A₂ t).card := by
    conv_lhs => rw [← hcover]
    simp only [rootBallUnion, Finset.union_biUnion]
    exact Finset.card_union_le _ _
  by_cases hfirst : u < (rootBallUnion P F W A₁ t).card
  · exact ⟨A₁, hsub, hcard₁ ▸ min_le_left _ _, hfirst⟩
  · refine ⟨A₂, Finset.sdiff_subset, hcard₂, ?_⟩
    have hcR : ((rootBallUnion P F W A t).card : ℝ) ≤
        (rootBallUnion P F W A₁ t).card + (rootBallUnion P F W A₂ t).card := by
      exact_mod_cast hcount
    linarith

theorem rootBallUnion_extract_root
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : V → Finset V) (g N : ℕ)
    (hFglobal : (F.card : ℝ) ≤ h * (Fintype.card V : ℝ) / 16)
    (hg : (Fintype.card V : ℝ) / 2 < (1 + h / (2 * (Fintype.card V : ℝ))) ^ g) :
    ∀ (A : Finset V) (t : ℕ),
      (∀ s ∈ A, s ∉ W s) →
      (∀ s ∈ A, ((W s).card : ℝ) ≤ h / 4) →
      A.card ≤ 2 ^ N →
      (Fintype.card V : ℝ) / 2 < (rootBallUnion P F W A t).card →
      ∃ s ∈ A, (Fintype.card V : ℝ) / 2 <
        (walkBall (avoidGraph P F (W s)) s (t + N * g)).card := by
  induction N with
  | zero =>
    intro A t hroots hW hcard hlarge
    have hne : A.Nonempty := by
      by_contra h
      have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he, rootBallUnion] at hlarge
      linarith
    obtain ⟨s, hs⟩ := hne
    have he : A = {s} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hs, fun v hv => (Finset.card_le_one.mp (by simpa using hcard)) v hv s hs⟩
    refine ⟨s, hs, ?_⟩
    simpa [he, rootBallUnion] using hlarge
  | succ N ih =>
    intro A t hroots hW hcard hlarge
    have hcard' : A.card ≤ 2 * 2 ^ N := by simpa [pow_succ, Nat.mul_comm] using hcard
    obtain ⟨A', hsub, hcard', hlarge'⟩ := rootBallUnion_halve P F W A t (2 ^ N)
      ((Fintype.card V : ℝ) / 4) hcard' (by linarith)
    have hF' : (F.card : ℝ) ≤ h * (rootBallUnion P F W A' t).card / 4 := by
      nlinarith
    have hpos : 1 ≤ (rootBallUnion P F W A' t).card := by
      have : 0 < ((rootBallUnion P F W A' t).card : ℝ) := by linarith
      exact_mod_cast this
    have hroots' : ∀ s ∈ A', s ∉ W s := fun s hs => hroots s (hsub hs)
    have hW' : ∀ s ∈ A', ((W s).card : ℝ) ≤ h / 4 := fun s hs => hW s (hsub hs)
    have hnext := rootBallUnion_growth_block P h hh.le hexp hr F W A' t g
      hroots' hW' hpos hF' hg
    obtain ⟨s, hs, hb⟩ := ih A' (t + g) hroots' hW' hcard' hnext
    refine ⟨s, hsub hs, ?_⟩
    have ht : t + (N + 1) * g = t + g + N * g := by ring
    simpa only [Nat.succ_eq_add_one, ht] using hb

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

noncomputable def routingG (r h : ℝ) : ℕ := ⌈8 * (r / h) * Real.logb 2 (2 * r)⌉₊

noncomputable def routingDepth (r : ℝ) : ℕ := ⌈Real.logb 2 r⌉₊

noncomputable def routingLength (r h : ℝ) : ℕ := 2 * routingG r h * (1 + routingDepth r)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

lemma le_two_pow_routingDepth (r : ℕ) (hr : 0 < r) : r ≤ 2 ^ routingDepth r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn := Nat.le_ceil (Real.logb 2 (r : ℝ))
  have hp := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hrR).mp hn
  rw [Real.rpow_natCast] at hp
  dsimp [routingDepth]
  exact_mod_cast hp

theorem routing_large_root_ball
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : V → Finset V) (S : Finset V)
    (hne : S.Nonempty)
    (hroots : ∀ s ∈ S, s ∉ W s)
    (hW : ∀ s ∈ S, ((W s).card : ℝ) ≤ h / 4)
    (hFstart : (F.card : ℝ) ≤ h * S.card / 4)
    (hFglobal : (F.card : ℝ) ≤ h * (Fintype.card V : ℝ) / 16) :
    ∃ s ∈ S, (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F (W s)) s
        (routingG (Fintype.card V) h * (1 + routingDepth (Fintype.card V)))).card := by
  have hrpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hg := routingG_growth (Fintype.card V) h (by exact_mod_cast (by omega : 1 ≤ Fintype.card V))
    hh (hexp.le_order P h hr)
  have hsub := roots_subset_rootBallUnion P F W S 0
  have hpos : 1 ≤ (rootBallUnion P F W S 0).card :=
    (Finset.card_pos.mpr hne).trans_le (Finset.card_le_card hsub)
  have hF : (F.card : ℝ) ≤ h * (rootBallUnion P F W S 0).card / 4 := by
    have hc : (S.card : ℝ) ≤ (rootBallUnion P F W S 0).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith
  have hb := rootBallUnion_growth_block P h hh.le hexp hrpos F W S 0
    (routingG (Fintype.card V) h) hroots hW hpos hF hg
  have hrootcard : S.card ≤ 2 ^ routingDepth (Fintype.card V) :=
    (Finset.card_le_univ S).trans (le_two_pow_routingDepth _ (by omega))
  obtain ⟨s, hs, hball⟩ := rootBallUnion_extract_root P h hh hexp hrpos F W
    (routingG (Fintype.card V) h) (routingDepth (Fintype.card V))
    hFglobal hg S (routingG (Fintype.card V) h) hroots hW hrootcard (by simpa using hb)
  refine ⟨s, hs, ?_⟩
  have ht : routingG (Fintype.card V) h * (1 + routingDepth (Fintype.card V)) =
      routingG (Fintype.card V) h + routingDepth (Fintype.card V) * routingG (Fintype.card V) h := by ring
  simpa only [ht] using hball

def incidentEdges (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

noncomputable def saturated (F : Finset (Sym2 V)) (h : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => h / 8 ≤ ((incidentEdges F v).card : ℝ))

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

def pathInterior {P : SimpleGraph V} {s t : V} (q : P.Walk s t) : Finset V :=
  q.support.toFinset \ {s, t}

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

def endpointLoad (A : Finset I) (x y : I → V) (v : V) : ℕ :=
  (A.filter (fun i => x i = v ∨ y i = v)).card

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

noncomputable def usedEdges (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) : Finset (Sym2 V) :=
  A.biUnion (fun i => (q i).edges.toFinset)

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

noncomputable def teamInterior (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) : Finset V :=
  (A.filter (fun j => team j = team i)).biUnion (fun j => pathInterior (q j))

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

structure PartialRoutes (P : SimpleGraph V) (x y : I → V) (team : I → T)
    (Z : I → Finset V) (L : ℕ) (h : ℝ) (A : Finset I)
    (q : ∀ i, P.Walk (x i) (y i)) : Prop where
  simple : ∀ i ∈ A, (q i).IsPath
  short : ∀ i ∈ A, (q i).length ≤ L
  avoids : ∀ i ∈ A, Disjoint (pathInterior (q i)) (Z i)
  edge_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset
  team_disjoint : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))
  degree : ∀ v, ((incidentEdges (usedEdges A q) v).card : ℝ) ≤ h / 8 + 2 + endpointLoad A x y v

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai.Batch

end
end
end

end OAI
