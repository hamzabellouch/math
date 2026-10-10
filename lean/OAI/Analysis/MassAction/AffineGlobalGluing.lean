import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.AffineGluing
import OAI.Analysis.MassAction.PowerAsymptotics
import OAI.Analysis.MassAction.IntervalGluing

namespace OAI

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace Problem326.Affine

/-- The cumulative shift assigned to a local family at level `j`. -/
def shiftedLabel {d : ℕ} (q : ℕ → ℝ) (j : ℕ) (L : Label d) : Label d :=
  ⟨L.slope, fun h => L.offset h - ∑ k ∈ Finset.range j, h ^ q k⟩

/-- Union of the shifted local families, with levels numbered `0, ..., N`. -/
def gluedFamily {d : ℕ} (N : ℕ) (q : ℕ → ℝ)
    (Λ : ℕ → Finset (Label d)) : Finset (Label d) := by
  classical
  exact (Finset.range (N + 1)).biUnion fun j => (Λ j).image (shiftedLabel q j)

@[simp] lemma shiftedLabel_slope {d : ℕ} (q : ℕ → ℝ) (j : ℕ) (L : Label d) :
    (shiftedLabel q j L).slope = L.slope := rfl

@[simp] lemma shiftedLabel_value {d : ℕ} (q : ℕ → ℝ) (j : ℕ)
    (L : Label d) (h : ℝ) (x : Fin d → ℝ) :
    (shiftedLabel q j L).value h x = L.value h x - ∑ k ∈ Finset.range j, h ^ q k := by
  unfold Label.value shiftedLabel
  dsimp
  ring

lemma shiftedLabel_mem_gluedFamily {d : ℕ} {N j : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} (hj : j ≤ N) (hL : L ∈ Λ j) :
    shiftedLabel q j L ∈ gluedFamily N q Λ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩

lemma mem_gluedFamily_iff {d : ℕ} {N : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} :
    L ∈ gluedFamily N q Λ ↔
      ∃ j ≤ N, ∃ J ∈ Λ j, shiftedLabel q j J = L := by
  classical
  simp only [gluedFamily, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, J, hJ, heq⟩
    exact ⟨j, by omega, J, hJ, heq⟩
  · rintro ⟨j, hj, J, hJ, heq⟩
    exact ⟨j, by omega, J, hJ, heq⟩

lemma active_gluedFamily_restrict {d : ℕ} {N j : ℕ} {q : ℕ → ℝ}
    {Λ : ℕ → Finset (Label d)} {L : Label d} {h : ℝ} {x : Fin d → ℝ}
    (hj : j ≤ N) (hL : L ∈ Λ j)
    (ha : Active (gluedFamily N q Λ) (shiftedLabel q j L) h x) :
    Active (Λ j) L h x := by
  refine ⟨hL, fun J hJ => ?_⟩
  have hc := ha.2 (shiftedLabel q j J) (shiftedLabel_mem_gluedFamily hj hJ)
  simpa only [shiftedLabel_value, sub_le_sub_iff_right] using hc

lemma gluedFamily_nonempty {d : ℕ} (N : ℕ) (q : ℕ → ℝ)
    (Λ : ℕ → Finset (Label d)) (hΛ : (Λ 0).Nonempty) :
    (gluedFamily N q Λ).Nonempty := by
  obtain ⟨L, hL⟩ := hΛ
  exact ⟨shiftedLabel q 0 L, shiftedLabel_mem_gluedFamily (Nat.zero_le N) hL⟩

/-- The full sequential approximation conclusion, with unrestricted approximating
exponent vectors, as required by the dimensional induction. -/
def Approximates {d : ℕ} (Λ : Finset (Label d)) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ L ∈ Λ, ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    ‖p₀ - L.slope‖ < E L.slope

/-- Compactness of the coordinate index supplies a least exponent. -/
lemma exists_hasMinimum {d : ℕ} (hd : 0 < d) (p : Fin d → ℝ) :
    ∃ t, HasMinimum p t := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.univ.exists_min_image p Finset.univ_nonempty
  exact ⟨p i, (fun j => hmin j (Finset.mem_univ _)), i, rfl⟩

/-- Assemble local fixed-minimum families into a global approximation family.
The two decay hypotheses are precisely those ensured by choosing each cut inside
both adjacent validity intervals. The local guarantees include the cut endpoints. -/
theorem gluedFamily_approximates {d N : ℕ} (hd : 0 < d)
    (t q : ℕ → ℝ) (Λ : ℕ → Finset (Label d)) (a b : ℝ)
    (E : (Fin d → ℝ) → ℝ)
    (hbaseline : ∀ j ≤ N, (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j)
    (hslope : ∀ j ≤ N, ∀ L ∈ Λ j, ∀ i, t j ≤ L.slope i)
    (hcenters : ∀ j < N, t j < t (j + 1))
    (hupperdecay : ∀ j < N, ∀ L ∈ Λ j,
      L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ q j))
    (hlowerdecay : ∀ j < N, ∀ L ∈ Λ (j + 1),
      L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ q j))
    (hlocal : ∀ j ≤ N, ∀ μ ∈ Set.Icc a b,
      (j = 0 ∨ q (j - 1) ≤ μ) → (j = N ∨ μ ≤ q j) →
      ApproximatesAtMinimum (Λ j) a b μ E) :
    Approximates (gluedFamily N q Λ) a b E := by
  intro L hL h p p₀ hpos hh hp hp₀ hactive
  obtain ⟨j, hj, J, hJ, rfl⟩ := mem_gluedFamily_iff.mp hL
  have hh' : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hpos⟩
  have hpeval : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)) :=
    tendsto_pi_nhds.mp hp
  obtain ⟨μ, hμ⟩ := exists_hasMinimum hd p₀
  have hupper : j = N ∨ μ ≤ q j := by
    by_cases hjN : j = N
    · exact Or.inl hjN
    right
    have hjlt : j < N := by omega
    have hcomparison : ∀ᶠ n in atTop,
        (∑ i, J.slope i * h n ^ p n i) + J.offset (h n) -
          (∑ k ∈ Finset.range j, h n ^ q k) ≤
        (∑ i : Fin d, t (j + 1) * h n ^ p n i) -
          (∑ k ∈ Finset.range (j + 1), h n ^ q k) := by
      apply Eventually.of_forall
      intro n
      have hc := (hactive n).2
        (shiftedLabel q (j + 1) ⟨fun _ => t (j + 1), fun _ => 0⟩)
        (shiftedLabel_mem_gluedFamily (by omega) (hbaseline (j + 1) (by omega)))
      simp only [shiftedLabel_value] at hc
      simpa only [Label.value, powerPoint, add_zero] using hc
    obtain ⟨i, hi⟩ := AffineGluing.shifted_active_upper_cut
      (fun k n => h n ^ q k) J.slope p₀ (t (j + 1)) (q j) j
      (Eventually.of_forall fun n => Real.rpow_pos_of_pos (hpos n) _)
      ((hupperdecay j hjlt J hJ).comp_tendsto hh')
      (fun i hgap => varying_rpow_isLittleO hh (Eventually.of_forall hpos) (hpeval i) hgap)
      hcomparison
    exact (hμ.1 i).trans hi
  have hlower : j = 0 ∨ q (j - 1) ≤ μ := by
    cases j with
    | zero => exact Or.inl rfl
    | succ k =>
      right
      have hk : k < N := by omega
      have hcomparison : ∀ᶠ n in atTop,
          (∑ i, J.slope i * h n ^ p n i) + J.offset (h n) -
            (∑ l ∈ Finset.range (k + 1), h n ^ q l) ≤
          (∑ i : Fin d, t k * h n ^ p n i) -
            (∑ l ∈ Finset.range k, h n ^ q l) := by
        apply Eventually.of_forall
        intro n
        have hc := (hactive n).2
          (shiftedLabel q k ⟨fun _ => t k, fun _ => 0⟩)
          (shiftedLabel_mem_gluedFamily (by omega) (hbaseline k (by omega)))
        simp only [shiftedLabel_value] at hc
        simpa only [Label.value, powerPoint, add_zero] using hc
      have hforced := AffineGluing.shifted_active_lower_cut
        (fun l n => h n ^ q l) J.slope p₀ (t k) (q k) k
        (fun i => (hcenters k hk).trans_le (hslope (k + 1) hj J hJ i))
        (Eventually.of_forall fun n => Real.rpow_pos_of_pos (hpos n) _)
        ((hlowerdecay k hk J hJ).comp_tendsto hh')
        (Eventually.of_forall fun n i => (Real.rpow_pos_of_pos (hpos n) (p n i)).le)
        (fun i hgap => tendsto_rpow_ratio_atTop hh (Eventually.of_forall hpos) (hpeval i) hgap)
        hcomparison
      obtain ⟨i, hi⟩ := hμ.2
      simpa only [Nat.add_sub_cancel, hi] using hforced i
  have hμab : μ ∈ Set.Icc a b := by
    obtain ⟨i, hi⟩ := hμ.2
    simpa only [Set.mem_Icc, hi] using hp₀ i
  have hresult := (hlocal j hj μ hμab hlower hupper) J hJ h p p₀ hpos hh hp hp₀ hμ
    (fun n => active_gluedFamily_restrict hj hJ (hactive n))
  simpa only [shiftedLabel_slope] using hresult

/-- Offset decay is preserved by the cumulative shifts because every cut
exponent lies strictly above the lower endpoint. -/
lemma shiftedLabel_offset_isLittleO {d : ℕ} {a : ℝ} (q : ℕ → ℝ)
    (j : ℕ) (L : Label d)
    (hL : L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a))
    (hq : ∀ k < j, a < q k) :
    (shiftedLabel q j L).offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a) := by
  have hsum : (fun h : ℝ => ∑ k ∈ Finset.range j, h ^ q k)
      =o[𝓝[>] 0] (fun h : ℝ => h ^ a) := by
    exact IsLittleO.fun_sum (fun k hk => rpow_isLittleO_at_zero (hq k (Finset.mem_range.mp hk)))
  exact hL.sub hsum

/-- Arbitrary local radius certificates
are glued into one nonempty finite family. No regularity of `ρ`, `Γ`, or `E` is
assumed. Local guarantees on open bands suffice because all cuts lie strictly
inside both neighboring bands. -/
theorem exists_approximating_family_of_local_families {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (ρ : ℝ → ℝ) (Γ : ℝ → Finset (Label d))
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t)
    (hbaseline : ∀ t ∈ Set.Icc a b,
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ t)
    (hdata : ∀ t ∈ Set.Icc a b, ∀ L ∈ Γ t,
      Cube a b L.slope ∧ HasMinimum L.slope t ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ t)))
    (hlocal : ∀ t ∈ Set.Icc a b, ∀ μ : ℝ, |μ - t| < ρ t →
      ApproximatesAtMinimum (Γ t) a b μ E) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a)) ∧
      Approximates Λ a b E := by
  classical
  obtain ⟨N, c, q, hc, hcmem, hfirst, hlast, hcuts⟩ :=
    IntervalGluing.exists_interval_gluing hab ρ hρ
  let t : ℕ → ℝ := fun j => if hj : j ≤ N then c ⟨j, by omega⟩ else a
  let Q : ℕ → ℝ := fun j => if hj : j < N then q ⟨j, hj⟩ else a
  let Λ : ℕ → Finset (Label d) := fun j => Γ (t j)
  have htm : ∀ j ≤ N, t j ∈ Set.Icc a b := by
    intro j hj
    simpa [t, hj] using hcmem ⟨j, by omega⟩
  have hcut : ∀ j < N, t j < Q j ∧ Q j < t (j + 1) ∧
      Q j ∈ Set.Ioo (t j - ρ (t j)) (t j + ρ (t j)) ∧
      Q j ∈ Set.Ioo (t (j + 1) - ρ (t (j + 1))) (t (j + 1) + ρ (t (j + 1))) := by
    intro j hj
    have hjle : j ≤ N := by omega
    have hjsucc : j + 1 ≤ N := by omega
    simpa [t, Q, hj, hjle, hjsucc] using hcuts ⟨j, hj⟩
  have hfirst' : a ∈ Set.Ioo (t 0 - ρ (t 0)) (t 0 + ρ (t 0)) := by
    simpa [t] using hfirst
  have hlast' : b ∈ Set.Ioo (t N - ρ (t N)) (t N + ρ (t N)) := by
    simpa [t, Fin.last] using hlast
  have hbase : ∀ j ≤ N,
      (⟨fun _ => t j, fun _ => 0⟩ : Label d) ∈ Λ j := by
    intro j hj
    exact hbaseline (t j) (htm j hj)
  have hlocal' : ∀ j ≤ N, ∀ μ ∈ Set.Icc a b,
      (j = 0 ∨ Q (j - 1) ≤ μ) → (j = N ∨ μ ≤ Q j) →
      ApproximatesAtMinimum (Λ j) a b μ E := by
    intro j hj μ hμ hlo hhi
    have hlo' : t j - ρ (t j) < μ := by
      by_cases hj0 : j = 0
      · subst j
        exact hfirst'.1.trans_le hμ.1
      · have hpred : j - 1 < N := by omega
        have hpredj : j - 1 + 1 = j := by omega
        have hprev : t j - ρ (t j) < Q (j - 1) := by
          simpa only [hpredj] using (hcut (j - 1) hpred).2.2.2.1
        exact hprev.trans_le (hlo.resolve_left hj0)
    have hhi' : μ < t j + ρ (t j) := by
      by_cases hjN : j = N
      · subst j
        exact hμ.2.trans_lt hlast'.2
      · have hjlt : j < N := by omega
        exact (hhi.resolve_left hjN).trans_lt (hcut j hjlt).2.2.1.2
    exact hlocal (t j) (htm j hj) μ (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have happrox : Approximates (gluedFamily N Q Λ) a b E := by
    apply gluedFamily_approximates hd t Q Λ a b E hbase
    · intro j hj L hL i
      exact (hdata (t j) (htm j hj) L hL).2.1.1 i
    · intro j hj
      exact (hcut j hj).1.trans (hcut j hj).2.1
    · intro j hj L hL
      exact ((hdata (t j) (htm j (by omega)) L hL).2.2).trans
        (rpow_isLittleO_at_zero (hcut j hj).2.2.1.2)
    · intro j hj L hL
      exact ((hdata (t (j + 1)) (htm (j + 1) (by omega)) L hL).2.2).trans
        (rpow_isLittleO_at_zero (hcut j hj).2.2.2.2)
    · exact hlocal'
  refine ⟨gluedFamily N Q Λ,
    gluedFamily_nonempty N Q Λ ⟨_, hbase 0 (Nat.zero_le N)⟩, ?_, happrox⟩
  intro L hL
  obtain ⟨j, hj, J, hJ, rfl⟩ := mem_gluedFamily_iff.mp hL
  have hJdata := hdata (t j) (htm j hj) J hJ
  refine ⟨hJdata.1, shiftedLabel_offset_isLittleO Q j J ?_ ?_⟩
  · exact hJdata.2.2.trans (rpow_isLittleO_at_zero (by
      have := hρ (t j) (htm j hj)
      have := (htm j hj).1
      linarith))
  · intro k hk
    exact (htm k (by omega)).1.trans_lt (hcut k (by omega)).1

/-- Choice-packaged form of the gluing theorem: local constructors may return
the radius and finite family existentially, and only for centers in the cube. -/
theorem exists_approximating_family_of_local_certificates {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hcert : ∀ t ∈ Set.Icc a b, ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Γ : Finset (Label d),
        (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ ∧
        (∀ L ∈ Γ, Cube a b L.slope ∧ HasMinimum L.slope t ∧
          L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ))) ∧
        (∀ μ : ℝ, |μ - t| < ρ → ApproximatesAtMinimum Γ a b μ E)) :
    ∃ Λ : Finset (Label d), Λ.Nonempty ∧
      (∀ L ∈ Λ, Cube a b L.slope ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ a)) ∧
      Approximates Λ a b E := by
  classical
  have hex : ∀ t : ℝ, ∃ ρ : ℝ, ∃ Γ : Finset (Label d),
      t ∈ Set.Icc a b → 0 < ρ ∧
        (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ ∧
        (∀ L ∈ Γ, Cube a b L.slope ∧ HasMinimum L.slope t ∧
          L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ))) ∧
        (∀ μ : ℝ, |μ - t| < ρ → ApproximatesAtMinimum Γ a b μ E) := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · obtain ⟨ρ, hρ, Γ, hΓ⟩ := hcert t ht
      exact ⟨ρ, Γ, fun _ => ⟨hρ, hΓ⟩⟩
    · exact ⟨1, ∅, fun h => (ht h).elim⟩
  choose ρ Γ hΓ using hex
  exact exists_approximating_family_of_local_families hd hab E ρ Γ
    (fun t ht => (hΓ t ht).1)
    (fun t ht => (hΓ t ht).2.1)
    (fun t ht => (hΓ t ht).2.2.1)
    (fun t ht => (hΓ t ht).2.2.2)

end Problem326.Affine

end

end OAI
