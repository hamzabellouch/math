import OAI.Probability.BenjaminiSchramm.CrossingExponentContinuity

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

lemma supermultiplicative_exp_rate_bound (P : ℝ → ℝ) (hP : ∀ t, 0 ≤ P t)
    (hzero : P 0 = 1) (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → P s*P t ≤ P (s+t))
    (β C : ℝ) (hbound : ∀ t, 0 ≤ t → P t ≤ C*Real.exp (-β*t))
    (t : ℝ) (ht : 0 ≤ t) : P t ≤ Real.exp (-β*t) := by
  have hpow (n : ℕ) : P t^n ≤ P ((n : ℝ)*t) := by
    induction n with
    | zero => simp only [pow_zero,Nat.cast_zero,zero_mul,hzero,le_refl]
    | succ n ih =>
      calc
        _ = P t^n*P t := pow_succ _ _
        _ ≤ P ((n : ℝ)*t)*P t := mul_le_mul_of_nonneg_right ih (hP t)
        _ ≤ P ((n : ℝ)*t+t) := hmul _ _ (mul_nonneg (Nat.cast_nonneg n) ht) ht
        _ = _ := by congr 1; push_cast; ring
  by_contra hn
  have hlt : Real.exp (-β*t) < P t := lt_of_not_ge hn
  have hone : 1 < P t*Real.exp (β*t) := by
    have hh := mul_lt_mul_of_pos_right hlt (Real.exp_pos (β*t))
    have he : Real.exp (-β*t)*Real.exp (β*t)=1 := by
      rw [←Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rwa [he] at hh
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hone).eventually
    (eventually_gt_atTop C)).exists
  have hh := mul_le_mul_of_nonneg_right
    ((hpow n).trans (hbound _ (mul_nonneg (Nat.cast_nonneg n) ht)))
    (pow_nonneg (Real.exp_pos (β*t)).le n)
  have he : Real.exp (-β*((n : ℝ)*t))*Real.exp (β*t)^n=1 := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [←mul_pow,mul_assoc,he,mul_one] at hh
  exact hn.not_ge hh

variable {V E : Type*} [Encodable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype (criticalModel G).VertexOrbit]

omit [Encodable V] in
theorem normalized_halfspace_uniform_of_infimal_bound
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (β : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) p t).toReal ≤ Real.exp (-β*t)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ (x : V) (t : ℝ), 0 ≤ t →
      (law p).real ((criticalModel G).adjustedHalfspaceHit
        ((criticalModel G).stationaryOrbitWeight μ) x (-r) t) ≤
        (p : ℝ)^(-(A*r+B)) * Real.exp (-β*t) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  obtain ⟨A,B,hA,hB,hpath⟩ := H.stationaryOrbitHeight_orbit_above hHc hl hHq μ hμ hstat hu
  have hauto := H.stationaryOrbitWeight_aut μ
  refine ⟨A,B,hA,hB,fun r hr x t ht => ?_⟩
  let α : ℝ := (p : ℝ)^(A*r+B)
  have hα : 0 < α := Real.rpow_pos_of_pos hp _
  have hroot (u : V) :
      α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) ≤
        (law p).real (H.adjustedHalfspaceHit a u 0 t) := by
    obtain ⟨y,w,horb,hlen,hw,hy⟩ := hpath r hr u (H.vertexOrbit x)
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact horb)
    change φ.vertex x = y at hφ
    have hcomp := H.adjustedHalfspaceHit_path_comparison hHc hl a p w r t hr hw hy
    have he := CriticalPercolation.BondGraph.Aut.adjustedHalfspaceHit_measure H a hauto φ p x (-r) t
    rw [hφ] at he
    have her := congrArg ENNReal.toReal he
    change (H.law p).real (H.adjustedHalfspaceHit a y (-r) t) =
      (H.law p).real (H.adjustedHalfspaceHit a x (-r) t) at her
    rw [her] at hcomp
    have hcoeff : α ≤ (p : ℝ)^w.length := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen
    exact (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg).trans hcomp
  have hmin : α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) ≤
      (H.infimalAdjustedCrossing a p t).toReal := by
    have he : ENNReal.ofReal (α*(law p).real (H.adjustedHalfspaceHit a x (-r) t)) ≤
        H.infimalAdjustedCrossing a p t := by
      apply le_iInf
      intro u
      exact ENNReal.ofReal_le_of_le_toReal (hroot u)
    have hf := ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a p t)) he
    have hnonneg : 0 ≤ α*(law p).real (H.adjustedHalfspaceHit a x (-r) t) :=
      mul_nonneg hα.le measureReal_nonneg
    rwa [ENNReal.toReal_ofReal hnonneg] at hf
  have hh := hmin.trans (hbound t ht)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hα.le)
  rw [← mul_assoc,inv_mul_cancel₀ hα.ne',one_mul] at hh'
  have he : α⁻¹ = (p : ℝ)^(-(A*r+B)) := by
    exact (Real.rpow_neg p.2.1 _).symm
  rwa [he] at hh'

theorem normalized_crossing_real_bound
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (p : unitInterval) (β : ℝ) (hβ : 0 ≤ β)
    (hbound : ∀ n : ℕ,
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) p n).toReal ≤ Real.exp (-β*n)) :
    ∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
      ((criticalModel G).stationaryOrbitWeight μ) p t).toReal ≤ Real.exp (-β*t) := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,hbounds⟩ := H.stationaryOrbitWeight_uniform_bounds
    (criticalModel_connected G hc) hl μ hμ
  have hne (t : ℝ) : H.infimalAdjustedCrossing a p t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a p t)
  have hmul (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      (H.infimalAdjustedCrossing a p s).toReal*(H.infimalAdjustedCrossing a p t).toReal ≤
        (H.infimalAdjustedCrossing a p (s+t)).toReal := by
    simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono (hne (s+t))
      (H.infimalAdjustedCrossing_supermultiplicative (criticalModel_connected G hc) hl
        (criticalModel_quasiTransitive G hq) a m M hm hbounds p hs ht)
  apply supermultiplicative_exp_rate_bound _ (fun _ => ENNReal.toReal_nonneg)
    (by simp only [H.infimalAdjustedCrossing_zero,ENNReal.toReal_one]) hmul β (Real.exp β)
  intro t ht
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hmono : H.infimalAdjustedCrossing a p t ≤ H.infimalAdjustedCrossing a p ⌊t⌋₊ := by
    apply iInf_mono
    intro x
    apply measure_mono
    rintro ω ⟨y,hy,hxy⟩
    exact ⟨y,hfloor.trans hy,hxy⟩
  calc
    _ ≤ (H.infimalAdjustedCrossing a p ⌊t⌋₊).toReal := ENNReal.toReal_mono (hne _) hmono
    _ ≤ Real.exp (-β*(⌊t⌋₊ : ℝ)) := hbound _
    _ ≤ Real.exp β*Real.exp (-β*t) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := Nat.lt_floor_add_one t
      nlinarith

theorem critical_normalized_exponent_ge_one
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) (α : ℝ)
    (hpos : ∀ n : ℕ, 0 < ((criticalModel G).infimalAdjustedCrossing
      ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α)) :
    1 ≤ α := by
  let H := criticalModel G
  let a := H.stationaryOrbitWeight μ
  obtain ⟨m,M,hm,hbounds⟩ := H.stationaryOrbitWeight_uniform_bounds
    (criticalModel_connected G hc) hl μ hμ
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hbound := critical_infimal_adjusted_crossing_bound G hc hl hq a
    (H.stationaryOrbitWeight_aut μ) m M hm hbounds n (Nat.cast_nonneg n)
  have hh := Real.log_le_log (hpos n) hbound
  rw [Real.log_exp] at hh
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  exact (le_div_iff₀ hnpos).mpr (by nlinarith)

theorem critical_normalized_exact_exponent
    (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (hu : ¬ (criticalModel G).CombinatoriallyUnimodular)
    (μ : (criticalModel G).VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep ((criticalModel G).orbitWalkKernel hl) μ = μ) :
    ∃ α : ℝ, 1 ≤ α ∧
      (∀ t : ℝ, 0 ≤ t → ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) t).toReal ≤ Real.exp (-α*t)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ ((criticalModel G).infimalAdjustedCrossing
          ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal) ∧
      Tendsto (fun n : ℕ => -Real.log ((criticalModel G).infimalAdjustedCrossing
        ((criticalModel G).stationaryOrbitWeight μ) (pc G) n).toReal/n) atTop (𝓝 α) := by
  let H := criticalModel G
  have hp : (0 : ℝ) < pc G := by exact_mod_cast pc_pos G hl hq
  obtain ⟨A,B,_hA,_hB,hpos⟩ := H.infimalAdjustedCrossing_finite_energy
    (criticalModel_connected G hc) hl (criticalModel_quasiTransitive G hq) μ hμ hstat hu (pc G) hp
  obtain ⟨α,hα,hupp,hlow,hlim⟩ := H.normalized_crossing_exponent
    (criticalModel_connected G hc) hl (criticalModel_quasiTransitive G hq) μ hμ hstat hu (pc G) hp
  refine ⟨α,critical_normalized_exponent_ge_one G hc hl hq μ hμ α
    (fun n => (Real.rpow_pos_of_pos hp _).trans_le (hpos n (Nat.cast_nonneg n))) hlim,
    normalized_crossing_real_bound G hc hl hq μ hμ (pc G) α hα hupp,hlow,hlim⟩

end Percolation.BenjaminiSchramm

end

end OAI
