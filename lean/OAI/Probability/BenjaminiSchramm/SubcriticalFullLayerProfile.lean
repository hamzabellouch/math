import OAI.Probability.BenjaminiSchramm.FullNegativeLayerProfile
import OAI.Probability.BenjaminiSchramm.SubcriticalLayerPrefactor

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma symmetric_exponential_profile (F : ℤ → ℝ≥0∞) (χ K D R β : ℝ)
    (hχ : 0 ≤ χ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hR : 0 < R) (hβ : R < β)
    (hbase : ∀ i, F i ≤ ENNReal.ofReal χ)
    (hup : ∀ n : ℕ, F n ≤ ENNReal.ofReal (K*χ*Real.exp (-β*n)))
    (hdown : ∀ n : ℕ, 3 ≤ n → F (-(n : ℤ)) ≤
      ENNReal.ofReal (D*K*χ*Real.exp (R+2*β)*Real.exp (-(β-R)*n))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℤ,
      F i ≤ ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|)) := by
  let a := β-R
  have ha : 0 < a := sub_pos.mpr hβ
  let M := χ+K*χ+D*K*χ*Real.exp (R+2*β)+1
  have hprod : 0 ≤ D*K*χ*Real.exp (R+2*β) := by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hχM : χ ≤ M := by dsimp [M]; nlinarith [mul_nonneg hK hχ]
  have hKM : K*χ ≤ M := by dsimp [M]; linarith
  have hDM : D*K*χ*Real.exp (R+2*β) ≤ M := by
    dsimp [M]
    linarith [mul_nonneg hK hχ]
  have hexp : (1 : ℝ) ≤ Real.exp (2*a) := Real.one_le_exp_iff.mpr (by positivity)
  have hMC : M ≤ M*Real.exp (2*a) := by nlinarith
  have hpos (n : ℕ) : F (n : ℤ) ≤
      ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*n)) := by
    apply (hup n).trans
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-β*n) ≤ Real.exp (-a*n) := by
      apply Real.exp_le_exp.mpr
      dsimp [a]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (mul_le_mul (hKM.trans hMC) he (Real.exp_nonneg _) (by positivity))
  have hneg (n : ℕ) : F (-(n : ℤ)) ≤
      ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*n)) := by
    by_cases hn : 3 ≤ n
    · exact (hdown n hn).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hDM.trans hMC) (Real.exp_nonneg _)))
    · apply (hbase _).trans
      apply ENNReal.ofReal_le_ofReal
      have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
      have he : (1 : ℝ) ≤ Real.exp (2*a-a*n) :=
        Real.one_le_exp_iff.mpr (by nlinarith)
      rw [mul_assoc,←Real.exp_add]
      have heq : 2*a + -a*(n : ℝ)=2*a-a*n := by ring
      rw [heq]
      exact hχM.trans (by nlinarith)
  refine ⟨M*Real.exp (2*a),by positivity,?_⟩
  intro i
  cases i with
  | ofNat n =>
    change F (n : ℤ) ≤ ENNReal.ofReal (M*Real.exp (2*a)*Real.exp (-a*|(n : ℝ)|))
    simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hpos n
  | negSucc n =>
    have hi : Int.negSucc n = -((n+1 : ℕ) : ℤ) := rfl
    simpa only [hi,Int.cast_neg,Int.cast_natCast,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))] using hneg (n+1)

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

theorem subcritical_full_layer_profile
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ=μ)
    (hu : ¬(criticalModel G).CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G e → w ∈ G e →
      |(criticalModel G).orbitAdjustedHeight ((criticalModel G).stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < pc G) :
    ∃ β : ℝ, R < β ∧ ∃ C : ℝ, 0 < C ∧ ∀ i : ℤ,
      (criticalModel G).supAdjustedFullLayerMoment ((criticalModel G).stationaryOrbitWeight μ) R p i ≤
        ENNReal.ofReal (C*Real.exp (-(β-R)*|(i : ℝ)|)) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨χ,hχ,hrow⟩ := subcritical_ennreal_row_bound G hl hq p hpc
  obtain ⟨β,hβ,_,K,hK,hup⟩ := subcritical_layer_prefactor G hc hl hq μ hμ hstat hu R hR hjump p hp hpc
  obtain ⟨m,M,hm,hweights⟩ := H.stationaryOrbitWeight_uniform_bounds hHc hl μ hμ
  let O := H.orbitRepresentatives hHq
  let D : ℝ≥0∞ := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hm))
    (ENNReal.sum_ne_top.mpr fun r _ => ENNReal.ofReal_ne_top)
  have hDEq : ENNReal.ofReal D.toReal=D := ENNReal.ofReal_toReal hD
  have hbase (i : ℤ) : H.supAdjustedFullLayerMoment a R p i ≤ ENNReal.ofReal χ :=
    H.supAdjustedFullLayerMoment_le_row_bound a R p _ hrow i
  have hpositive (n : ℕ) : H.supAdjustedFullLayerMoment a R p n ≤
      ENNReal.ofReal (K*χ*Real.exp (-β*n)) := by
    apply (H.supAdjustedFullLayerMoment_up_bound hHc hl a R hR hjump p _ hrow n).trans
    apply (mul_le_mul' (hup n) le_rfl).trans_eq
    rw [←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _))]
    congr 1
    ring
  have hnegative (n : ℕ) (hn : 3 ≤ n) : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
      ENNReal.ofReal (D.toReal*K*χ*Real.exp (R+2*β)*Real.exp (-(β-R)*n)) := by
    have hb : H.supAdjustedFullLayerMoment a R p (-(n : ℤ)) ≤
        D*ENNReal.ofReal (Real.exp (R*((n : ℝ)+1)))*
          (H.supAdjustedUpLayerMoment a R p (n-2)*ENNReal.ofReal χ) := by
      apply iSup_le
      intro x
      apply iSup_le
      intro u
      exact H.adjustedFullLayerMoment_negative_bound O hHc hl a
        (H.stationaryOrbitWeight_pos hHc hl μ hμ) (H.stationaryOrbitWeight_aut μ)
        m hm (fun x => (hweights x).1) R hR hjump p _ hrow n hn x u
    apply hb.trans
    apply (mul_le_mul' le_rfl (mul_le_mul' (hup (n-2)) le_rfl)).trans_eq
    nth_rw 1 [←hDEq]
    rw [←ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ←ENNReal.ofReal_mul (mul_nonneg hK.le (Real.exp_nonneg _)),
      ←ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _))]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    rw [show D.toReal*Real.exp (R*((n : ℝ)+1))*(K*Real.exp (-β*((n : ℝ)-2))*χ) =
      D.toReal*K*χ*(Real.exp (R*((n : ℝ)+1))*Real.exp (-β*((n : ℝ)-2))) by ring,
      ←Real.exp_add,show R*((n : ℝ)+1)+ -β*((n : ℝ)-2) = R+2*β + (-(β-R)*(n : ℝ)) by ring,
      Real.exp_add]
    ring
  obtain ⟨C,hC,hprof⟩ := symmetric_exponential_profile
    (H.supAdjustedFullLayerMoment a R p) χ K D.toReal R β hχ hK.le ENNReal.toReal_nonneg
      hR hβ hbase hpositive hnegative
  exact ⟨β,hβ,C,hC,hprof⟩

end Percolation.BenjaminiSchramm

end

end OAI
