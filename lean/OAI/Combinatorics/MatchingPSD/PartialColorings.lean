import OAI.Combinatorics.MatchingPSD.EdgeMonomials

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorCounting
variable {V : Type u_1} {C : Type u_2} [Fintype V]

omit [Fintype V] in
lemma swap_preserves_color (z : V → C) {a b : V} (hab : z a = z b) (v : V) :
    z (Equiv.swap a b v) = z v := by
  by_cases hva : v = a
  · subst v; simpa using hab.symm
  by_cases hvb : v = b
  · subst v; simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne hva hvb]

omit [Fintype V] in
lemma swap_fixes_finset (U : Finset V) {a b : V} (ha : a ∉ U) (hb : b ∉ U)
    (v : V) (hv : v ∈ U) : Equiv.swap a b v = v :=
  Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hv)) (fun h => hb (h ▸ hv))

omit [Fintype V] in
lemma exists_color_perm_fixing_pair (z : V → C) (U : Finset V)
    {a b c d : V} (ha : a ∉ U) (hb : b ∉ U) (hc : c ∉ U) (hd : d ∉ U)
    (hab : a ≠ b) (hcd : c ≠ d) (hzac : z a = z c) (hzbd : z b = z d) :
    ∃ p : colorStabilizer z, (∀ v ∈ U, p.1 v = v) ∧ p.1 a = c ∧ p.1 b = d := by
  let q := Equiv.swap a c
  have hq : ∀ v, z (q v) = z v := swap_preserves_color z hzac
  have hqfix : ∀ v ∈ U, q v = v := swap_fixes_finset U ha hc
  have hqb : q b ∉ U := by
    intro h
    have hh := hqfix (q b) h
    have : b = q b := by simpa only [q, Equiv.swap_apply_self] using hh
    exact hb (this ▸ h)
  let p := Equiv.swap (q b) d * q
  have hp : p ∈ colorStabilizer z := by
    intro v
    change z (Equiv.swap (q b) d (q v)) = z v
    rw [swap_preserves_color z ((hq b).trans hzbd), hq]
  refine ⟨⟨p, hp⟩, ?_, ?_, ?_⟩
  · intro v hv
    change Equiv.swap (q b) d (q v) = v
    rw [hqfix v hv, swap_fixes_finset U hqb hd v hv]
  · change Equiv.swap (q b) d (q a) = c
    have hqbc : q b ≠ c := by
      change Equiv.swap a c b ≠ c
      intro h
      have hh := congrArg (Equiv.swap a c) h
      have : b = a := by simpa using hh
      exact hab this.symm
    rw [show q a = c by simp [q]]
    exact Equiv.swap_apply_of_ne_of_ne hqbc.symm hcd
  · change Equiv.swap (q b) d (q b) = d
    simp

noncomputable def tableCoordinate (z : V → C) (c : C × C) (M : Pairing V) : ℝ :=
  ∑ v, if z v = c.1 ∧ z (M.1 v) = c.2 then 1 else 0

lemma tableCoordinate_invariant (z : V → C) (c : C × C) (p : colorStabilizer z) :
    Pairing.act p.1 (tableCoordinate z c) = tableCoordinate z c := by
  funext M
  simp only [Pairing.act_apply, tableCoordinate, Pairing.relabel_apply, inv_inv]
  have hi (v : V) : z (p.1⁻¹ v) = z v := (p⁻¹).property v
  simp_rw [hi]
  rw [← Equiv.sum_comp p.1 (fun v => if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  rw [p.property]

noncomputable def candidateEdges (z : V → C) (U : Finset V) (c : C × C) : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧ z e.1 = c.1 ∧ z e.2 = c.2

lemma mem_candidateEdges (z : V → C) (U : Finset V) (c : C × C) (e : V × V) :
    e ∈ candidateEdges z U c ↔
      e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧ z e.1 = c.1 ∧ z e.2 = c.2 := by
  simp [candidateEdges]

lemma candidate_average_eq (z : V → C) (l : List (V × V)) (c : C × C)
    (e f : V × V) (he : e ∈ candidateEdges z (Pairing.edgeSupport l) c)
    (hf : f ∈ candidateEdges z (Pairing.edgeSupport l) c) :
    colorAverage z (Pairing.edgeMonomial (e::l)) =
      colorAverage z (Pairing.edgeMonomial (f::l)) := by
  obtain ⟨ha, hb, hab, hza, hzb⟩ := (mem_candidateEdges _ _ _ _).mp he
  obtain ⟨hc, hd, hcd, hzc, hzd⟩ := (mem_candidateEdges _ _ _ _).mp hf
  obtain ⟨p, hp, hpa, hpb⟩ := exists_color_perm_fixing_pair z (Pairing.edgeSupport l)
    ha hb hc hd hab hcd (hza.trans hzc.symm) (hzb.trans hzd.symm)
  rw [← colorAverage_act z p (Pairing.edgeMonomial (e::l)), Pairing.edgeMonomial_cons]
  have hact : Pairing.act p.1 (Pairing.edgeCoord e * Pairing.edgeMonomial l) =
      Pairing.edgeCoord f * Pairing.edgeMonomial l := by
    rw [Pairing.act_pointwise_mul, Pairing.edgeMonomial_act_fix l p.1 hp,
      Pairing.act_edgeCoord, hpa, hpb]
  rw [hact, Pairing.edgeMonomial_cons]

lemma candidate_sum (z : V → C) (U : Finset V) (c : C × C) (M : Pairing V)
    (hU : ∀ v, M.1 v ∈ U ↔ v ∈ U) :
    ∑ e ∈ candidateEdges z U c, Pairing.edgeCoord e M =
      ∑ v ∈ (Finset.univ \ U), if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0 := by
  rw [candidateEdges, Finset.sum_filter]
  change (∑ e : V × V, if e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧
      z e.1 = c.1 ∧ z e.2 = c.2 then Pairing.edgeCoord e M else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]
  have hpoint (v : V) :
      (∑ w : V, if v ∉ U ∧ w ∉ U ∧ v ≠ w ∧ z v = c.1 ∧ z w = c.2
        then Pairing.edgeCoord (v,w) M else 0) =
      if v ∉ U then (if z v = c.1 ∧ z (M.1 v) = c.2 then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single (M.1 v)]
    · by_cases hv : v ∈ U <;> by_cases ha : z v = c.1 <;>
        by_cases hb : z (M.1 v) = c.2 <;>
        simp [Pairing.edgeCoord, hU v, (M.partner_ne v).symm, hv, ha, hb]
    · intro w _ hw
      simp [Pairing.edgeCoord, Ne.symm hw]
    · simp
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun v => v ∉ U) = Finset.univ \ U := by ext; simp
  rw [hfilter, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]

lemma monomial_candidate_identity (z : V → C) (l : List (V × V)) (c : C × C)
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    Pairing.edgeMonomial l * (∑ e ∈ candidateEdges z (Pairing.edgeSupport l) c,
      Pairing.edgeCoord e) =
    Pairing.edgeMonomial l * (tableCoordinate z c -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = c.1 ∧ z (M₀.1 v) = c.2 then (1:ℝ) else 0) • 1) := by
  funext M
  by_cases hm : Pairing.ContainsList M l
  · simp only [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, ite_eq_left hm, one_mul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [candidate_sum z (Pairing.edgeSupport l) c M (fun v => ⟨
      fun hv => by simpa using Pairing.contains_partner_support hm hv,
      fun hv => Pairing.contains_partner_support hm hv⟩)]
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    unfold tableCoordinate
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [Pairing.contains_agree_support hm h₀ hv]
  · simp [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, hm]

end ColorCounting
end MatchingSmoothing

end OAI
