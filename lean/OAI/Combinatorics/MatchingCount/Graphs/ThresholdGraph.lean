import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.FillHoles

namespace OAI

namespace MatchingFPRAS.Switching

open Finset

variable {V : Type*}

lemma edgeActivity_of_symmetric [LinearOrder V] (B : V → V → ℝ)
    (hB : ∀ a b, B a b = B b a) (a b : V) : edgeActivity B a b = B a b := by
  unfold edgeActivity
  split_ifs
  · rfl
  · exact hB b a

theorem erasePair_factor [Fintype V] [LinearOrder V] (B : V → V → ℝ)
    (hB : ∀ a b, B a b = B b a) (q : Mate V) (a b : V)
    (hq : q.val a = b) (hab : a ≠ b) :
    weight B q = B a b * weight B (erasePair q a b) := by
  have ha : (erasePair q a b).val a = a := by simp [hq]
  have hb : (erasePair q a b).val b = b := by simp [hq]
  have hw := withEdge_weight B (erasePair q a b) a b ha hb hab
  rw [withEdge_erasePair q a b hq,edgeActivity_of_symmetric B hB] at hw
  exact hw

lemma ultrametric_vertex_charge {A C D T : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hAT : A ≤ T) (hCT : C ≤ T) (htri : min A C ≤ D) :
    A*C ≤ T*D := by
  rcases le_total A C with h | h
  · rw [min_eq_left h] at htri
    exact (mul_le_mul htri hCT hC hD).trans_eq (mul_comm D T)
  · rw [min_eq_right h] at htri
    exact mul_le_mul hAT htri hC (hA.trans hAT)

lemma ultrametric_pair_charge {A B C D Tj Tk : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAj : A ≤ Tj) (hBk : B ≤ Tk) (hCj : C ≤ Tj) (hCk : C ≤ Tk)
    (htri : min A (min C B) ≤ D) : A*B*C ≤ Tj*Tk*D := by
  have hj0 := hA.trans hAj
  have hk0 := hB.trans hBk
  rcases le_total A (min C B) with h | h
  · rw [min_eq_left h] at htri
    calc
      A*B*C ≤ D*Tk*Tj := by gcongr
      _ = Tj*Tk*D := by ring
  · rw [min_eq_right h] at htri
    rcases le_total C B with hcb | hbc
    · rw [min_eq_left hcb] at htri
      gcongr
    · rw [min_eq_right hbc] at htri
      calc
        A*B*C ≤ Tj*D*Tk := by gcongr
        _ = Tj*Tk*D := by ring

lemma pairing_mate_mem [Fintype V] [DecidableEq V] (q : Mate V) (U : Finset V)
    (hq : HasHoles q Uᶜ) (v : V) : q.val v ∈ U ↔ v ∈ U := by
  have h := mate_mem_holes_iff q Uᶜ hq v
  simpa only [Finset.mem_compl, not_iff_not] using h

theorem pairing_replace_vertex [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (T : ℝ) (hT : ∀ a, a ≠ j → B j a ≤ T)
    (q : Mate V) (hq : HasHoles q Uᶜ) :
    ∃ q' : Mate V, HasHoles q' (insert u (U.erase j))ᶜ ∧
      weight B q * B j u ≤ T * weight B q' := by
  classical
  let a := q.val j
  have hja : j ≠ a := by
    intro h
    exact (Finset.mem_compl.mp ((hq j).mp h.symm)) hj
  have haU : a ∈ U := (pairing_mate_mem q U hq j).mpr hj
  have hua : u ≠ a := fun h => hu (h ▸ haU)
  have huj : u ≠ j := fun h => hu (h ▸ hj)
  have hqj : q.val j = a := rfl
  have hqa : q.val a = j := mate_mate q j
  have hqu : q.val u = u := (hq u).mpr (Finset.mem_compl.mpr hu)
  let r := erasePair q j a
  have hra : r.val a = a := by simp [r,hqj]
  have hru : r.val u = u := by simp [r,hqj,huj,hua,hqu]
  let q' := withEdge r u a
  have he (v) : q'.val v = if v = u then a else if v = a then u
      else if v = j ∨ v = a then v else q.val v := by
    rw [show q'.val v = (withEdge r u a).val v from rfl,
      withEdge_apply r u a v hru hra,erasePair_apply q j a v hqj]
    split_ifs <;> rfl
  refine ⟨q',?_,?_⟩
  · intro v
    rw [he]
    by_cases hvu : v = u
    · subst v
      simp [hua.symm]
    by_cases hva : v = a
    · subst v
      simp [hvu,hua,haU,hja.symm]
    by_cases hvj : v = j
    · subst v
      simp [hvu,hva]
    simp only [hvu,hva,hvj,false_or,↓reduceIte]
    rw [hq]
    simp [hvu,hvj]
  · have hwq := erasePair_factor B hB q j a hqj hja
    have hwq' : weight B q' = B u a * weight B r := by
      simpa only [q',edgeActivity_of_symmetric B hB] using withEdge_weight B r u a hru hra hua
    have ht : min (B j a) (B j u) ≤ B u a := by
      have hh := htri u a j hua huj hja.symm
      simpa only [hB u j,min_comm] using hh
    have hh := ultrametric_vertex_charge (hB0 j a) (hB0 j u) (hB0 u a)
      (hT a hja.symm) (hT u huj) ht
    have hr0 := weight_nonneg B hB0 r
    have hf := mul_le_mul_of_nonneg_right hh hr0
    rw [hwq,hwq']
    dsimp only [r] at hf
    nlinarith only [hf]

theorem pairing_remove_pair [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
    (Tj Tk : ℝ) (hTj : ∀ a, a ≠ j → B j a ≤ Tj)
    (hTk : ∀ a, a ≠ k → B k a ≤ Tk)
    (q : Mate V) (hq : HasHoles q Uᶜ) :
    ∃ q' : Mate V, HasHoles q' (U \ {j,k})ᶜ ∧
      weight B q * B j k ≤ Tj * Tk * weight B q' := by
  classical
  have hcj : B j k ≤ Tj := hTj k hjk.symm
  have hck : B j k ≤ Tk := (hB j k).trans_le (hTk j hjk)
  by_cases hqjk : q.val j = k
  · let q' := erasePair q j k
    refine ⟨q',?_,?_⟩
    · have hh := erasePair_holes q Uᶜ hq j k hqjk
      have he : insert j (insert k Uᶜ) = (U \ {j,k})ᶜ := by ext v; simp; tauto
      rwa [he] at hh
    · rw [erasePair_factor B hB q j k hqjk hjk]
      have hv := weight_nonneg B hB0 q'
      change (B j k * weight B q') * B j k ≤ _
      calc
        _ = (B j k * B j k) * weight B q' := by ring
        _ ≤ (Tj*Tk) * weight B q' := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul hcj hck (hB0 j k) ((hB0 j k).trans hcj)) hv
  · let a := q.val j
    let b := q.val k
    have hqj : q.val j = a := rfl
    have hqk : q.val k = b := rfl
    have hqa : q.val a = j := mate_mate q j
    have hqb : q.val b = k := mate_mate q k
    have hja : j ≠ a := by
      intro h
      exact (Finset.mem_compl.mp ((hq j).mp h.symm)) hj
    have hkb : k ≠ b := by
      intro h
      exact (Finset.mem_compl.mp ((hq k).mp h.symm)) hk
    have hak : a ≠ k := hqjk
    have hbj : b ≠ j := by
      intro h
      have hh := congrArg q.val h
      rw [hqb,hqj] at hh
      exact hak hh.symm
    have hab : a ≠ b := by
      intro h
      have hh := congrArg q.val h
      rw [hqa,hqb] at hh
      exact hjk hh
    have haU : a ∈ U := (pairing_mate_mem q U hq j).mpr hj
    have hbU : b ∈ U := (pairing_mate_mem q U hq k).mpr hk
    let r := erasePair q j a
    have hrk : r.val k = b := by simp [r,hqj,hjk.symm,hak.symm,hqk]
    let z := erasePair r k b
    have hza : z.val a = a := by
      rw [show z.val a = (erasePair r k b).val a from rfl, erasePair_apply r k b a hrk]
      simp [hak,hab,r,hqj]
    have hzb : z.val b = b := by simp [z,hrk]
    let q' := withEdge z a b
    have he (v) : q'.val v = if v = a then b else if v = b then a
        else if v = k ∨ v = b then v else if v = j ∨ v = a then v else q.val v := by
      rw [show q'.val v = (withEdge z a b).val v from rfl,
        withEdge_apply z a b v hza hzb,erasePair_apply r k b v hrk,
        erasePair_apply q j a v hqj]
      split_ifs <;> rfl
    refine ⟨q',?_,?_⟩
    · intro v
      rw [he]
      by_cases hva : v = a
      · subst v
        simp [hab.symm,haU,hja.symm,hak]
      by_cases hvb : v = b
      · subst v
        simp [hva,hab,hbU,hbj,hkb.symm]
      by_cases hvj : v = j
      · subst v
        simp [hva,hvb]
      by_cases hvk : v = k
      · subst v
        simp [hva,hvb]
      simp only [hva,hvb,hvj,hvk,false_or,↓reduceIte]
      rw [hq]
      simp [hvj,hvk]
    · have hwq := erasePair_factor B hB q j a hqj hja
      have hwr := erasePair_factor B hB r k b hrk hkb
      have hwq' : weight B q' = B a b * weight B z := by
        simpa only [q',edgeActivity_of_symmetric B hB] using withEdge_weight B z a b hza hzb hab
      have ht : min (B j a) (min (B j k) (B k b)) ≤ B a b := by
        calc
          _ ≤ min (B j a) (B j b) :=
            min_le_min_left _ (htri j b k hbj.symm hjk hkb.symm)
          _ = min (B a j) (B j b) := by rw [hB j a]
          _ ≤ _ := htri a b j hab hja.symm hbj
      have hh := ultrametric_pair_charge (hB0 j a) (hB0 k b) (hB0 j k) (hB0 a b)
        (hTj a hja.symm) (hTk b hkb.symm) hcj hck ht
      have hz0 := weight_nonneg B hB0 z
      have hf := mul_le_mul_of_nonneg_right hh hz0
      rw [hwq,show weight B (erasePair q j a) = weight B r from rfl,hwr,hwq']
      change (B j a * (B k b * weight B z)) * B j k ≤ Tj*Tk*(B a b*weight B z)
      nlinarith only [hf]

lemma weight_le_pairingCapacity [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (U : Finset V) (hU : Even U.card)
    (q : Mate V) (hq : HasHoles q Uᶜ) : weight B q ≤ pairingCapacity B U hU := by
  exact Finset.le_sup' _ ((mem_matchings q Uᶜ).mpr hq)

lemma pairingCapacity_nonneg [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, 0 ≤ B a b)
    (U : Finset V) (hU : Even U.card) : 0 ≤ pairingCapacity B U hU := by
  obtain ⟨q,hq⟩ := pairing_exists U hU
  exact (weight_nonneg B hB q).trans (weight_le_pairingCapacity B U hU q hq)

theorem capacity_replace_vertex [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (hU' : Even (insert u (U.erase j)).card)
    (T : ℝ) (hT0 : 0 ≤ T) (hT : ∀ a, a ≠ j → B j a ≤ T) :
    pairingCapacity B U hU * B j u ≤ T * pairingCapacity B (insert u (U.erase j)) hU' := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Uᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists U hU
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight B)
  have hcap : pairingCapacity B U hU = weight B q := hmax
  obtain ⟨q',hq',hle⟩ := pairing_replace_vertex B hB hB0 htri U j u hj hu T hT q
    ((mem_matchings _ _).mp hq)
  rw [hcap]
  exact hle.trans (mul_le_mul_of_nonneg_left
    (weight_le_pairingCapacity B _ hU' q' hq') hT0)

theorem capacity_remove_pair [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a)
    (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
    (hU' : Even (U \ {j,k}).card)
    (Tj Tk : ℝ) (hj0 : 0 ≤ Tj) (hk0 : 0 ≤ Tk)
    (hTj : ∀ a, a ≠ j → B j a ≤ Tj) (hTk : ∀ a, a ≠ k → B k a ≤ Tk) :
    pairingCapacity B U hU * B j k ≤ Tj * Tk * pairingCapacity B (U \ {j,k}) hU' := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Uᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists U hU
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight B)
  have hcap : pairingCapacity B U hU = weight B q := hmax
  obtain ⟨q',hq',hle⟩ := pairing_remove_pair B hB hB0 htri U j k hj hk hjk Tj Tk hTj hTk q
    ((mem_matchings _ _).mp hq)
  rw [hcap]
  exact hle.trans (mul_le_mul_of_nonneg_left
    (weight_le_pairingCapacity B _ hU' q' hq') (mul_nonneg hj0 hk0))

def thresholdGraph [LinearOrder V] (w : V → V → ℝ) (t : ℝ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ t ≤ edgeActivity w a b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa only [edgeActivity_comm w b a] using h.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

lemma strong_walk_reachable [LinearOrder V] (w : V → V → ℝ) (t : ℝ)
    {a b : V} (p : (⊤ : SimpleGraph V).Walk a b)
    (hp : ∀ d ∈ p.darts, t ≤ edgeActivity w d.fst d.snd) :
    (thresholdGraph w t).Reachable a b := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac p ih =>
    have he : t ≤ edgeActivity w a c := hp ⟨(a,c),hac⟩ (by simp)
    have htail : ∀ d ∈ p.darts, t ≤ edgeActivity w d.fst d.snd := by
      intro d hd
      exact hp d (by simp [hd])
    exact (SimpleGraph.Adj.reachable (G := thresholdGraph w t)
      ⟨by simpa using hac,he⟩).trans (ih htail)

lemma threshold_map_strong [LinearOrder V] (w : V → V → ℝ) (t : ℝ)
    {a b : V} (p : (thresholdGraph w t).Walk a b) :
    ∀ d ∈ (p.map (SimpleGraph.Hom.ofLE le_top)).darts,
      t ≤ edgeActivity w d.fst d.snd := by
  intro d hd
  rw [SimpleGraph.Walk.darts_map] at hd
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  exact e.adj.2

theorem bottleneck_threshold [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) (t : ℝ) (ht : 1 < t) :
    t ≤ bottleneck w a b ↔ (thresholdGraph w t).Reachable a b := by
  classical
  constructor
  · intro h
    obtain ⟨p,hp,hmax⟩ := Finset.exists_mem_eq_sup'
      (show (Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).Nonempty from
        ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
      (pathStrength w hab)
    have he : t ≤ pathStrength w hab p := by
      unfold bottleneck at h
      rw [dite_eq_right hab,hmax] at h
      exact (le_max_iff.mp h).resolve_left (not_le_of_gt ht)
    apply strong_walk_reachable w t p.val
    intro d hd
    exact he.trans (Finset.inf'_le _ (List.mem_toFinset.mpr hd))
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    let q : (⊤ : SimpleGraph V).Path a b :=
      ⟨p.map (SimpleGraph.Hom.ofLE le_top),hp.map Function.injective_id⟩
    have hstr : t ≤ pathStrength w hab q := by
      apply Finset.le_inf'
      intro d hd
      exact threshold_map_strong w t p d (List.mem_toFinset.mp hd)
    unfold bottleneck
    rw [dite_eq_right hab]
    exact hstr.trans ((Finset.le_sup' _ (Finset.mem_univ q)).trans (le_max_right _ _))

theorem bottleneck_comm [Fintype V] [LinearOrder V] (w : V → V → ℝ) (a b : V) :
    bottleneck w a b = bottleneck w b a := by
  by_cases hab : a = b
  · subst b; rfl
  apply le_antisymm
  · by_cases h : 1 < bottleneck w a b
    · exact (bottleneck_threshold w b a (Ne.symm hab) _ h).mpr
        (((bottleneck_threshold w a b hab _ h).mp le_rfl).symm)
    · exact (le_of_not_gt h).trans (one_le_bottleneck w b a)
  · by_cases h : 1 < bottleneck w b a
    · exact (bottleneck_threshold w a b hab _ h).mpr
        (((bottleneck_threshold w b a (Ne.symm hab) _ h).mp le_rfl).symm)
    · exact (le_of_not_gt h).trans (one_le_bottleneck w a b)

theorem bottleneck_ultrametric [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    min (bottleneck w a c) (bottleneck w c b) ≤ bottleneck w a b := by
  let t := min (bottleneck w a c) (bottleneck w c b)
  by_cases ht : 1 < t
  · apply (bottleneck_threshold w a b hab t ht).mpr
    exact ((bottleneck_threshold w a c hac t ht).mp (min_le_left _ _)).trans
      ((bottleneck_threshold w c b hbc.symm t ht).mp (min_le_right _ _))
  · exact (le_of_not_gt ht).trans (one_le_bottleneck w a b)

theorem capacity_charged_remove [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j k : V) (hj : j ∈ U) (hk : k ∈ U)
    (hjk : j ≠ k) (hU' : Even (U \ {j,k}).card) (Tj Tk f : ℝ)
    (hj0 : 0 < Tj) (hk0 : 0 < Tk) (hTj : ∀ a, a ≠ j → B j a ≤ Tj)
    (hTk : ∀ a, a ≠ k → B k a ≤ Tk) (hf : f*Tj*Tk ≤ B j k) :
    pairingCapacity B U hU * f ≤ pairingCapacity B (U \ {j,k}) hU' := by
  have hc := capacity_remove_pair B hB hB0 htri U hU j k hj hk hjk hU'
    Tj Tk hj0.le hk0.le hTj hTk
  have hs := mul_le_mul_of_nonneg_left hf (pairingCapacity_nonneg B hB0 U hU)
  have hprod : 0 < Tj*Tk := mul_pos hj0 hk0
  apply (mul_le_mul_iff_of_pos_right hprod).mp
  calc
    _ = pairingCapacity B U hU * (f*Tj*Tk) := by ring
    _ ≤ pairingCapacity B U hU * B j k := hs
    _ ≤ _ := by nlinarith only [hc]

theorem capacity_charged_replace [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    (U : Finset V) (hU : Even U.card) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
    (hU' : Even (insert u (U.erase j)).card) (T f : ℝ)
    (hT0 : 0 < T) (hT : ∀ a, a ≠ j → B j a ≤ T) (hf : f*T ≤ B j u) :
    pairingCapacity B U hU * f ≤ pairingCapacity B (insert u (U.erase j)) hU' := by
  have hc := capacity_replace_vertex B hB hB0 htri U hU j u hj hu hU' T hT0.le hT
  have hs := mul_le_mul_of_nonneg_left hf (pairingCapacity_nonneg B hB0 U hU)
  apply (mul_le_mul_iff_of_pos_right hT0).mp
  calc
    _ = pairingCapacity B U hU * (f*T) := by ring
    _ ≤ pairingCapacity B U hU * B j u := hs
    _ ≤ _ := by nlinarith only [hc]

inductive ChargeTrace [DecidableEq V] (B : V → V → ℝ) :
    Finset V → Finset V → ℝ → Prop
  | done (U) : ChargeTrace B U U 1
  | remove (U W : Finset V) (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k)
      (Tj Tk f F : ℝ) (hj0 : 0 < Tj) (hk0 : 0 < Tk) (hf0 : 0 ≤ f) (hF0 : 0 ≤ F)
      (hTj : ∀ a, a ≠ j → B j a ≤ Tj) (hTk : ∀ a, a ≠ k → B k a ≤ Tk)
      (hf : f*Tj*Tk ≤ B j k) (next : ChargeTrace B (U \ {j,k}) W F) :
      ChargeTrace B U W (f*F)
  | replace (U W : Finset V) (j u : V) (hj : j ∈ U) (hu : u ∉ U)
      (T f F : ℝ) (hT0 : 0 < T) (hf0 : 0 ≤ f) (hF0 : 0 ≤ F)
      (hT : ∀ a, a ≠ j → B j a ≤ T) (hf : f*T ≤ B j u)
      (next : ChargeTrace B (insert u (U.erase j)) W F) :
      ChargeTrace B U W (f*F)

lemma ChargeTrace.card_le [DecidableEq V] {B : V → V → ℝ}
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) : W.card ≤ U.card := by
  induction h with
  | done => rfl
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    exact ih.trans (Finset.card_le_card Finset.sdiff_subset)
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have hnu : u ∉ U.erase j := fun h => hu (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hnu,Finset.card_erase_of_mem hj] at ih
    have : 0 < U.card := Finset.card_pos.mpr ⟨j,hj⟩
    omega

lemma even_remove_two [DecidableEq V] (U : Finset V) (hU : Even U.card)
    (j k : V) (hj : j ∈ U) (hk : k ∈ U) (hjk : j ≠ k) :
    Even (U \ {j,k}).card := by
  have he : U \ {j,k} = (U.erase j).erase k := by ext a; simp; tauto
  have hk' : k ∈ U.erase j := Finset.mem_erase.mpr ⟨hjk.symm,hk⟩
  rw [he,Finset.card_erase_of_mem hk',Finset.card_erase_of_mem hj]
  have h2 : 2 ≤ U.card := by
    apply (Finset.card_pair hjk).symm.trans_le
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  exact (Nat.even_iff.mpr (by have := Nat.even_iff.mp hU; omega))

lemma even_replace_one [DecidableEq V] (U : Finset V) (hU : Even U.card)
    (j u : V) (hj : j ∈ U) (hu : u ∉ U) : Even (insert u (U.erase j)).card := by
  have hnu : u ∉ U.erase j := fun h => hu (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hnu,Finset.card_erase_of_mem hj]
  have : 0 < U.card := Finset.card_pos.mpr ⟨j,hj⟩
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ U.card)] using hU

theorem ChargeTrace.capacity_bound [Fintype V] [LinearOrder V]
    {B : V → V → ℝ} (hB : ∀ a b, B a b = B b a) (hB0 : ∀ a b, 0 ≤ B a b)
    (htri : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → min (B a c) (B c b) ≤ B a b)
    {U W : Finset V} {F : ℝ} (h : ChargeTrace B U W F) (hU : Even U.card) :
    ∃ hW : Even W.card, pairingCapacity B U hU * F ≤ pairingCapacity B W hW := by
  induction h with
  | done U => exact ⟨hU,by simp⟩
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    have he := even_remove_two U hU j k hj hk hjk
    obtain ⟨hW,hWb⟩ := ih he
    refine ⟨hW,?_⟩
    calc
      _ = (pairingCapacity B U hU * f) * F := by ring
      _ ≤ pairingCapacity B (U \ {j,k}) he * F := mul_le_mul_of_nonneg_right
        (capacity_charged_remove B hB hB0 htri U hU j k hj hk hjk he Tj Tk f
          hj0 hk0 hTj hTk hf) hF0
      _ ≤ _ := hWb
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have he := even_replace_one U hU j u hj hu
    obtain ⟨hW,hWb⟩ := ih he
    refine ⟨hW,?_⟩
    calc
      _ = (pairingCapacity B U hU * f) * F := by ring
      _ ≤ pairingCapacity B (insert u (U.erase j)) he * F := mul_le_mul_of_nonneg_right
        (capacity_charged_replace B hB hB0 htri U hU j u hj hu he T f hT0 hT hf) hF0
      _ ≤ _ := hWb

theorem edgeActivity_le_bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) :
    edgeActivity w a b ≤ bottleneck w a b := by
  by_cases h : 1 < edgeActivity w a b
  · exact (bottleneck_threshold w a b hab _ h).mpr
      (SimpleGraph.Adj.reachable (G := thresholdGraph w _) ⟨hab,le_rfl⟩)
  · exact (le_of_not_gt h).trans (one_le_bottleneck w a b)

theorem bottleneck_le_row_bound [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a : V) (T : ℝ) (hT : 1 ≤ T)
    (hrow : ∀ b, a ≠ b → edgeActivity w a b ≤ T) (b : V) :
    bottleneck w a b ≤ T := by
  by_cases hab : a = b
  · subst b; simpa [bottleneck] using hT
  by_cases hB : 1 < bottleneck w a b
  · obtain ⟨L,hL,hnd,hb⟩ := bottleneck_path w a b hab hB
    cases L with
    | nil => simp at hb
    | cons c L =>
      have hne : a ≠ c := by
        have h := (List.nodup_cons.mp hnd).1
        simp only [List.mem_cons,not_or] at h
        exact h.1
      have he := (List.isChain_cons_cons.mp hL).1
      exact he.trans (hrow c hne)
  · exact (le_of_not_gt hB).trans hT

theorem bottleneck_eq_of_threshold_iff
    {W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (w : V → V → ℝ) (w' : W → W → ℝ) (a b : V) (a' b' : W)
    (hab : a ≠ b) (hab' : a' ≠ b')
    (h : ∀ t : ℝ, 1 < t →
      ((thresholdGraph w t).Reachable a b ↔ (thresholdGraph w' t).Reachable a' b')) :
    bottleneck w a b = bottleneck w' a' b' := by
  apply le_antisymm
  · by_cases ht : 1 < bottleneck w a b
    · exact (bottleneck_threshold w' a' b' hab' _ ht).mpr
        ((h _ ht).mp ((bottleneck_threshold w a b hab _ ht).mp le_rfl))
    · exact (le_of_not_gt ht).trans (one_le_bottleneck w' a' b')
  · by_cases ht : 1 < bottleneck w' a' b'
    · exact (bottleneck_threshold w a b hab _ ht).mpr
        ((h _ ht).mpr ((bottleneck_threshold w' a' b' hab' _ ht).mp le_rfl))
    · exact (le_of_not_gt ht).trans (one_le_bottleneck w a b)

def pairVertices (xs : List (V × V)) : List V := xs.flatMap (fun q => [q.1,q.2])

lemma ChargeTrace.trans [DecidableEq V] {B : V → V → ℝ}
    {U W X : Finset V} {F G : ℝ} (h : ChargeTrace B U W F)
    (h' : ChargeTrace B W X G) (hG : 0 ≤ G) : ChargeTrace B U X (F*G) := by
  induction h with
  | done U => simpa using h'
  | remove U W j k hj hk hjk Tj Tk f F hj0 hk0 hf0 hF0 hTj hTk hf next ih =>
    have ht := ChargeTrace.remove U X j k hj hk hjk Tj Tk f (F*G) hj0 hk0 hf0
      (mul_nonneg hF0 hG) hTj hTk hf (ih h')
    simpa [mul_assoc] using ht
  | replace U W j u hj hu T f F hT0 hf0 hF0 hT hf next ih =>
    have ht := ChargeTrace.replace U X j u hj hu T f (F*G) hT0 hf0
      (mul_nonneg hF0 hG) hT hf (ih h')
    simpa [mul_assoc] using ht

theorem charge_remove_list [DecidableEq V] (B : V → V → ℝ) (T : V → ℝ)
    (f : V × V → ℝ) (xs : List (V × V)) (U : Finset V)
    (hnd : (pairVertices xs).Nodup) (hsub : ∀ a ∈ pairVertices xs, a ∈ U)
    (hlocal : ∀ q ∈ xs,
      0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → B q.2 a ≤ T q.2) ∧ f q*T q.1*T q.2 ≤ B q.1 q.2) :
    ChargeTrace B U (U \ (pairVertices xs).toFinset) (xs.map f).prod := by
  induction xs generalizing U with
  | nil => simpa [pairVertices] using ChargeTrace.done (B := B) U
  | cons q xs ih =>
    obtain ⟨j,k⟩ := q
    have hn : j ≠ k ∧ j ∉ pairVertices xs ∧ k ∉ pairVertices xs ∧ (pairVertices xs).Nodup := by
      simpa [pairVertices,List.nodup_cons,and_assoc] using hnd
    have hj : j ∈ U := hsub j (by simp [pairVertices])
    have hk : k ∈ U := hsub k (by simp [pairVertices])
    have hs : ∀ a ∈ pairVertices xs, a ∈ U \ {j,k} := by
      intro a ha
      have haj : a ≠ j := fun he => hn.2.1 (he ▸ ha)
      have hak : a ≠ k := fun he => hn.2.2.1 (he ▸ ha)
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨hsub a (by simp [pairVertices] at ha ⊢; exact Or.inr (Or.inr ha)),haj,hak⟩
    have hl : ∀ q ∈ xs,
      0 < T q.1 ∧ 0 < T q.2 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧
      (∀ a, a ≠ q.2 → B q.2 a ≤ T q.2) ∧ f q*T q.1*T q.2 ≤ B q.1 q.2 :=
      fun q hq => hlocal q (List.mem_cons_of_mem _ hq)
    have ht := ih (U \ {j,k}) hn.2.2.2 hs hl
    have hp : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hl q hq).2.2.1
    have he : (U \ {j,k}) \ (pairVertices xs).toFinset =
        U \ (pairVertices ((j,k)::xs)).toFinset := by
      ext a
      simp [pairVertices]
      tauto
    obtain ⟨hTj,hTk,hf,hjrow,hkrow,hbound⟩ := hlocal (j,k) (by simp)
    have hr := ChargeTrace.remove U _ j k hj hk hn.1 (T j) (T k) (f (j,k))
      (xs.map f).prod hTj hTk hf hp hjrow hkrow hbound ht
    simpa only [List.map_cons,List.prod_cons,he] using hr

theorem charge_replace_list [DecidableEq V] (B : V → V → ℝ) (T : V → ℝ)
    (f : V × V → ℝ) (xs : List (V × V)) (U : Finset V)
    (hsrc : (xs.map Prod.fst).Nodup) (hdst : (xs.map Prod.snd).Nodup)
    (hsub : ∀ q ∈ xs, q.1 ∈ U) (hfresh : ∀ q ∈ xs, q.2 ∉ U)
    (hlocal : ∀ q ∈ xs, 0 < T q.1 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧ f q*T q.1 ≤ B q.1 q.2) :
    ChargeTrace B U ((U \ (xs.map Prod.fst).toFinset) ∪ (xs.map Prod.snd).toFinset)
      (xs.map f).prod := by
  induction xs generalizing U with
  | nil => simpa using ChargeTrace.done (B := B) U
  | cons q xs ih =>
    obtain ⟨j,u⟩ := q
    have hsrc' : j ∉ xs.map Prod.fst ∧ (xs.map Prod.fst).Nodup := by simpa using hsrc
    have hdst' : u ∉ xs.map Prod.snd ∧ (xs.map Prod.snd).Nodup := by simpa using hdst
    have hj : j ∈ U := hsub (j,u) (by simp)
    have hu : u ∉ U := hfresh (j,u) (by simp)
    have hs : ∀ q ∈ xs, q.1 ∈ insert u (U.erase j) := by
      intro q hq
      have hn : q.1 ≠ j := by
        intro he; exact hsrc'.1 (he ▸ List.mem_map.mpr ⟨q,hq,rfl⟩)
      simp only [Finset.mem_insert,Finset.mem_erase]
      exact Or.inr ⟨hn,hsub q (by simp [hq])⟩
    have hf : ∀ q ∈ xs, q.2 ∉ insert u (U.erase j) := by
      intro q hq
      have hn : q.2 ≠ u := by
        intro he; exact hdst'.1 (he ▸ List.mem_map.mpr ⟨q,hq,rfl⟩)
      simp only [Finset.mem_insert,Finset.mem_erase,not_or,not_and]
      exact ⟨hn,fun _ => hfresh q (by simp [hq])⟩
    have hl : ∀ q ∈ xs, 0 < T q.1 ∧ 0 ≤ f q ∧
      (∀ a, a ≠ q.1 → B q.1 a ≤ T q.1) ∧ f q*T q.1 ≤ B q.1 q.2 :=
      fun q hq => hlocal q (List.mem_cons_of_mem _ hq)
    have ht := ih (insert u (U.erase j)) hsrc'.2 hdst'.2 hs hf hl
    have hp : 0 ≤ (xs.map f).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      exact (hl q hq).2.1
    have hus : u ∉ xs.map Prod.fst := by
      rintro h
      obtain ⟨q,hq,he⟩ := List.mem_map.mp h
      exact hu (he ▸ hsub q (by simp [hq]))
    have he : ((insert u (U.erase j)) \ (xs.map Prod.fst).toFinset) ∪ (xs.map Prod.snd).toFinset =
        (U \ (((j,u)::xs).map Prod.fst).toFinset) ∪ (((j,u)::xs).map Prod.snd).toFinset := by
      ext a
      by_cases hau : a=u
      · subst a; simp [hus]
      · simp only [List.map_cons,List.toFinset_cons,Finset.mem_union,Finset.mem_sdiff,
          Finset.mem_insert,Finset.mem_erase,List.mem_toFinset,hau,false_or]
        tauto
    obtain ⟨hT,hf0,hrow,hbound⟩ := hlocal (j,u) (by simp)
    have hr := ChargeTrace.replace U _ j u hj hu (T j) (f (j,u)) (xs.map f).prod
      hT hf0 hp hrow hbound ht
    simpa only [List.map_cons,List.prod_cons,he] using hr

end MatchingFPRAS.Switching

end OAI
