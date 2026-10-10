import OAI.Combinatorics.TreewidthL1.CobagEmbedding

namespace OAI

namespace BoundedTreewidthL1
variable {V : Type*} (G : SimpleGraph V)

/-- Removing empty bags preserves the exact tree-decomposition hypotheses.
The graph is only required to be nonempty and connected; no extra metric
hypothesis enters this combinatorial reduction. -/
theorem nonempty_tree_decomposition [Fintype V] [DecidableEq V] [Nonempty V]
    (hG : G.Connected) (k : ℕ) (hdec : HasTreeDecomposition G k) :
    ∃ n : ℕ, ∃ T : SimpleGraph (Fin n), ∃ bag : Fin n → Finset V,
      T.IsTree ∧
      (∀ v : V, ∃ t, v ∈ bag t) ∧
      (∀ u v : V, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      (∀ v : V, (T.induce {t | v ∈ bag t}).Connected) ∧
      (∀ t, (bag t).card ≤ k) ∧ (∀ t, (bag t).Nonempty) := by
  classical
  obtain ⟨n, T, B, hT, hcover, hedge, hocc, hsize⟩ := hdec
  let S : Set (Fin n) := {i | (B i).Nonempty}
  have hS : (T.induce S).Connected := by
    have hc : (G.induce Set.univ).Connected := G.induceUnivIso.connected_iff.mpr hG
    have := touched_bags_connected_set G T B hedge hocc Set.univ hc
    have heq : {t | ∃ z ∈ (Set.univ : Set V), z ∈ B t} = S := by
      ext t
      simp [S, Finset.nonempty_def]
    rw [heq] at this
    exact this
  let I := {i : Fin n // i ∈ S}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let T' : SimpleGraph (Fin (Fintype.card I)) := (T.induce S).comap e
  let B' : Fin (Fintype.card I) → Finset V := fun i => B (e i).val
  have hT' : T'.IsTree :=
    (SimpleGraph.Iso.comap e (T.induce S)).isTree_iff.mpr ⟨hS, hT.isAcyclic.induce S⟩
  refine ⟨Fintype.card I, T', B', hT', ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨i, hi⟩ := hcover v
    refine ⟨e.symm ⟨i, v, hi⟩, ?_⟩
    simpa [B'] using hi
  · intro u v huv
    obtain ⟨i, hui, hvi⟩ := hedge u v huv
    refine ⟨e.symm ⟨i, u, hui⟩, ?_, ?_⟩ <;> simpa [B']
  · intro v
    let f : {i : Fin n // v ∈ B i} → {j : Fin (Fintype.card I) // v ∈ B' j} :=
      fun i => ⟨e.symm ⟨i.val, v, i.property⟩, by simpa [B'] using i.property⟩
    let hf : (T.induce {i | v ∈ B i}) →g (T'.induce {j | v ∈ B' j}) :=
      ⟨f, by
        intro i j hij
        change T.Adj (e (f i).val).val (e (f j).val).val
        simpa [f] using hij⟩
    apply (hocc v).map hf
    intro j
    refine ⟨⟨(e j.val).val, j.property⟩, ?_⟩
    apply Subtype.ext
    change e.symm _ = j.val
    rw [Equiv.symm_apply_eq]
  · intro i
    exact hsize _
  · intro i
    exact (e i).property

end BoundedTreewidthL1

namespace BoundedTreewidthL1
noncomputable section

/-- Direct sum of two finite real L1 vectors, with the sum norm (not the maximum
norm on an ordinary product). -/
def l1Append {m n : ℕ} (x : PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (y : PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) :
    PiLp (1 : ENNReal) (fun _ : Fin (m+n) => ℝ) :=
  WithLp.toLp 1 (Fin.append x.ofLp y.ofLp)

lemma l1Append_norm_sub {m n : ℕ} (x x' : PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (y y' : PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) :
    ‖l1Append x y-l1Append x' y'‖ = ‖x-x'‖+‖y-y'‖ := by
  simp only [PiLp.norm_eq_sum (by simp : 0 < (1 : ENNReal).toReal), ENNReal.toReal_one,
    Real.rpow_one, div_self (by norm_num : (1:ℝ) ≠ 0)]
  rw [Fin.sum_univ_add]
  simp [l1Append, PiLp.sub_apply]

/-- The final purely metric bridge: a common-bag bound on both endpoints and
co-bag separation imply a global all-pairs lower comparison. -/
lemma common_bag_comparison {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    {I : Type*} (B : I → Finset V) (hne : ∀ i, (B i).Nonempty)
    {m n : ℕ} (Φ : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (Ψ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ))
    (U c a : ℝ) (hU : 0 ≤ U) (hc : 0 < c) (ha : 0 < a)
    (hupper : ∀ x y, ‖Ψ x-Ψ y‖ ≤ U*shortestPathDistance G ℓ x y)
    (hcobag : ∀ i x y, x ∈ B i → y ∈ B i →
      c*shortestPathDistance G ℓ x y ≤ ‖Ψ x-Ψ y‖)
    (hanchor : ∀ x y, ∃ i, a*bagDistance G ℓ (B i) (hne i) x ≤ ‖Φ x-Φ y‖ ∧
      a*bagDistance G ℓ (B i) (hne i) y ≤ ‖Φ x-Φ y‖) (x y : V) :
    c*shortestPathDistance G ℓ x y ≤
      ‖Ψ x-Ψ y‖ + (2*(U+c)/a)*‖Φ x-Φ y‖ := by
  obtain ⟨i,hix,hiy⟩ := hanchor x y
  obtain ⟨p,hp,hpx⟩ := bagDistance_attained G ℓ (B i) (hne i) x
  obtain ⟨q,hq,hqy⟩ := bagDistance_attained G ℓ (B i) (hne i) y
  have hd := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le) x p y
  have hd' := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le) p q y
  have hs := shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le) q y
  have hΨ := norm_sub_le_norm_sub_add_norm_sub (Ψ p) (Ψ x) (Ψ q)
  have hΨ' := norm_sub_le_norm_sub_add_norm_sub (Ψ x) (Ψ y) (Ψ q)
  have hxp := hupper x p
  have hyq := hupper y q
  rw [norm_sub_rev (Ψ p) (Ψ x)] at hΨ
  have hco := hcobag i p q hp hq
  rw [← hpx] at hd hxp
  rw [hs,← hqy] at hd'
  rw [← hqy] at hyq
  have hda : a*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) ≤
      2*‖Φ x-Φ y‖ := by linarith
  have hmain : c*shortestPathDistance G ℓ x y ≤ ‖Ψ x-Ψ y‖+
      (U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) := by
    nlinarith
  have hsum : (U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) ≤
      (2*(U+c)/a)*‖Φ x-Φ y‖ := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have hh := mul_le_mul_of_nonneg_left hda (by linarith : 0 ≤ U+c)
    calc
      a*((U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y)) =
        (U+c)*(a*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y)) := by ring
      _ ≤ (U+c)*(2*‖Φ x-Φ y‖) := hh
      _ = a*((2*(U+c)/a)*‖Φ x-Φ y‖) := by field_simp
  exact hmain.trans (add_le_add le_rfl hsum)

end
end BoundedTreewidthL1

namespace BoundedTreewidthL1
noncomputable section

theorem main_theorem : MainStatement := by
  classical
  intro k hk
  obtain ⟨Ua,ca,hUa,hca,hanchor⟩ := AnchorExperiment.anchor_common_bag_embedding k hk
  obtain ⟨Ub,cb,hUb,hcb,hcobag⟩ := cobag_embedding k hk
  let lam : ℝ := 2*(Ub+cb)/ca
  have hlam : 0 < lam := by dsimp [lam]; positivity
  let C : ℝ := max 1 ((lam*Ua+Ub)/cb)
  refine ⟨C,le_max_left _ _,?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ
  rcases subsingleton_or_nontrivial V with hsub | hnontriv
  · let := hsub
    refine ⟨0,fun _ => 0,?_⟩
    intro x y
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    simp [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)]
  · let := hnontriv
    obtain ⟨n,T,B,hT,hcover,hedge,hrun,hbag,hne⟩ := nonempty_tree_decomposition G hG k hdec
    cases n with
    | zero =>
      obtain ⟨i,_⟩ := hcover (Classical.choice (inferInstance : Nonempty V))
      exact Fin.elim0 i
    | succ n =>
      let root : Fin (n+1) := ⟨0,Nat.succ_pos n⟩
      obtain ⟨ma,Φ,hΦu,hΦa⟩ := hanchor V G hG ℓ hℓ n T hT root B hne hcover hedge hrun hbag
      obtain ⟨mb,Ψ,hΨu,hΨb⟩ := hcobag V G hG ℓ hℓ (n+1) T hT root B hcover hedge hrun hbag
      let F : V → PiLp (1 : ENNReal) (fun _ : Fin (ma+mb) => ℝ) :=
        fun x => cb⁻¹ • l1Append (lam • Φ x) (Ψ x)
      refine ⟨ma+mb,F,?_⟩
      intro x y
      have hnorm : ‖F x-F y‖ = cb⁻¹*(lam*‖Φ x-Φ y‖+‖Ψ x-Ψ y‖) := by
        dsimp only [F]
        rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hcb),
          l1Append_norm_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hlam]
      rw [hnorm]
      constructor
      · have hh := common_bag_comparison G hG ℓ hℓ B hne Φ Ψ Ub cb ca hUb.le hcb hca
          hΨu hΨb hΦa x y
        have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hcb.le)
        simpa only [← mul_assoc, inv_mul_cancel₀ hcb.ne',one_mul,add_comm] using hh'
      · calc
          cb⁻¹*(lam*‖Φ x-Φ y‖+‖Ψ x-Ψ y‖) ≤
              cb⁻¹*(lam*(Ua*shortestPathDistance G ℓ x y)+Ub*shortestPathDistance G ℓ x y) :=
            mul_le_mul_of_nonneg_left (add_le_add
              (mul_le_mul_of_nonneg_left (hΦu x y) hlam.le) (hΨu x y)) (inv_nonneg.mpr hcb.le)
          _ = ((lam*Ua+Ub)/cb)*shortestPathDistance G ℓ x y := by ring
          _ ≤ C*shortestPathDistance G ℓ x y := mul_le_mul_of_nonneg_right (le_max_right _ _)
            (shortestPathDistance_nonneg G ℓ hG (fun e => (hℓ e).le) x y)

end
end BoundedTreewidthL1

end OAI
