import Mathlib

namespace OAI

                                 
section

                                                                               
                                                                            
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def bumpB (σ v : ℝ) : ℝ := max 0 (min 1 (2-v/σ))
def bumpA (σ R v : ℝ) : ℝ :=
  if v ≤ R then min (v^2/σ^2) 1 else if v ≤ 2*R then 2-v/R else 0
def gate (R v : ℝ) : ℝ := max 0 (min 1 (v/(10*R)-1))
def feasible (r σ R : ℝ) (z : X → ℝ) : Prop :=
  (∀ s, 0 ≤ z s) ∧
  (∀ p, (∑ s, max (z s-gate R (dist s p/r)) 0) ≤ 1) ∧
  (∀ s s', s ≠ s' → 0 < z s → 0 < z s' → 5*σ*r ≤ dist s s')
def integrand (r σ R : ℝ) (g z : X → ℝ) (p : X) : ℝ :=
  (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) +
    256*∑ s, z s*(1+g s)*bumpA σ R (dist s p/r)
def objective (r σ R : ℝ) (μ g z : X → ℝ) : ℝ :=
  r*∑ p, μ p*integrand r σ R g z p
def value (r σ R : ℝ) (μ g : X → ℝ) : ℝ :=
  sInf (objective r σ R μ g '' {z : X → ℝ | feasible r σ R z})

theorem gate_nonneg (R v : ℝ) : 0 ≤ gate R v := le_max_left _ _
theorem gate_zero (R : ℝ) : gate R 0 = 0 := by simp [gate]

theorem zero_feasible (r σ R : ℝ) : feasible (X := X) r σ R (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, ?_, ?_⟩
  · intro p
    have hg : ∀ s : X, max (0-gate R (dist s p/r)) 0 = 0 := by
      intro s
      exact max_eq_right (by linarith [gate_nonneg R (dist s p/r)])
    simp only [hg, Finset.sum_const_zero]
    norm_num
  · intro s s' hss hs
    linarith

theorem feasible_upper (r σ R : ℝ) (z : X → ℝ) (hz : feasible r σ R z) (s : X) :
    z s ≤ 1 := by
  have hs : max (z s-gate R (dist s s/r)) 0 ≤
      ∑ t, max (z t-gate R (dist t s/r)) 0 :=
    Finset.single_le_sum (f := fun t => max (z t-gate R (dist t s/r)) 0)
      (fun t ht => le_max_right _ _) (Finset.mem_univ s)
  have hg : max (z s-gate R (dist s s/r)) 0 = z s := by
    simp [gate, max_eq_left (hz.1 s)]
  rw [hg] at hs
  exact hs.trans (hz.2.1 s)

theorem feasible_closed_form (r σ R : ℝ) (z : X → ℝ) :
    feasible r σ R z ↔ (∀ s, 0 ≤ z s) ∧
      (∀ p, (∑ s, max (z s-gate R (dist s p/r)) 0) ≤ 1) ∧
      (∀ s s', s ≠ s' → dist s s' < 5*σ*r → z s*z s' = 0) := by
  constructor
  · rintro ⟨hn, hc, hs⟩
    refine ⟨hn, hc, ?_⟩
    intro s s' hne hdist
    rcases (hn s).eq_or_lt with hz | hp
    · rw [← hz]; ring
    rcases (hn s').eq_or_lt with hz | hp'
    · rw [← hz]; ring
    linarith [hs s s' hne hp hp']
  · rintro ⟨hn, hc, hs⟩
    refine ⟨hn, hc, ?_⟩
    intro s s' hne hp hp'
    by_contra h
    have he := hs s s' hne (lt_of_not_ge h)
    have hm := mul_pos hp hp'
    linarith

theorem feasible_isClosed (r σ R : ℝ) : IsClosed {z : X → ℝ | feasible r σ R z} := by
  simp only [feasible_closed_form, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  · apply IsClosed.inter
    · apply isClosed_iInter
      intro p
      apply isClosed_le _ continuous_const
      fun_prop
    · apply isClosed_iInter
      intro s
      apply isClosed_iInter
      intro s'
      apply isClosed_iInter
      intro hne
      apply isClosed_iInter
      intro hdist
      exact isClosed_eq ((continuous_apply s).mul (continuous_apply s')) continuous_const

theorem feasible_isCompact (r σ R : ℝ) : IsCompact {z : X → ℝ | feasible r σ R z} := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : X => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hc.of_isClosed_subset (feasible_isClosed r σ R)
  intro z hz s hs
  exact ⟨hz.1 s, feasible_upper r σ R z hz s⟩

theorem objective_continuous (r σ R : ℝ) (μ g : X → ℝ) :
    Continuous (objective r σ R μ g) := by
  unfold objective integrand
  fun_prop

theorem minimum_exists (r σ R : ℝ) (μ g : X → ℝ) :
    ∃ z, feasible r σ R z ∧ objective r σ R μ g z = value r σ R μ g ∧
      ∀ w, feasible r σ R w → objective r σ R μ g z ≤ objective r σ R μ g w := by
  obtain ⟨z, hz, hmin⟩ := (feasible_isCompact (X := X) r σ R).exists_isMinOn
    ⟨fun _ => 0, zero_feasible r σ R⟩ (objective_continuous r σ R μ g).continuousOn
  refine ⟨z, hz, ?_, hmin⟩
  have hleast : IsLeast (objective r σ R μ g '' {w | feasible r σ R w})
      (objective r σ R μ g z) := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmin hw
  exact hleast.csInf_eq.symm

theorem value_le (r σ R : ℝ) (μ g z : X → ℝ) (hz : feasible r σ R z) :
    value r σ R μ g ≤ objective r σ R μ g z := by
  obtain ⟨w, hw, he, hmin⟩ := minimum_exists r σ R μ g
  rw [← he]
  exact hmin z hz

theorem bumpB_bounds (σ v : ℝ) : bumpB σ v ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem bumpA_bounds (σ R v : ℝ) (hR : 0 < R) :
    bumpA σ R v ∈ Set.Icc (0:ℝ) 1 := by
  unfold bumpA
  split_ifs with hv hv'
  · exact ⟨le_min (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num), min_le_right _ _⟩
  · have hdiv₁ : 1 ≤ v/R := (le_div_iff₀ hR).mpr (by linarith)
    have hdiv₂ : v/R ≤ 2 := (div_le_iff₀ hR).mpr (by linarith)
    constructor <;> linarith
  · exact ⟨le_rfl, by norm_num⟩

theorem gate_eq_zero (R v : ℝ) (hR : 0 < R) (hv : v ≤ 10*R) : gate R v = 0 := by
  have hdiv : v/(10*R) ≤ 1 := (div_le_iff₀ (by positivity : 0 < 10*R)).mpr (by linarith)
  unfold gate
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem bumpB_zero (σ v : ℝ) (hσ : 0 < σ) (hv : 2*σ ≤ v) : bumpB σ v = 0 := by
  have hd : 2 ≤ v/σ := (le_div_iff₀ hσ).mpr hv
  unfold bumpB
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem bumpA_zero (σ R v : ℝ) (hR : 0 < R) (hv : 2*R ≤ v) : bumpA σ R v = 0 := by
  unfold bumpA
  have hnot : ¬v ≤ R := by linarith
  rw [ite_eq_right hnot]
  split_ifs with hv'
  · have he : v = 2*R := by linarith
    rw [he]
    field_simp
    ring
  · rfl

theorem weighted_bumpB (σ R v z : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hz : 0 ≤ z) :
    z*bumpB σ v ≤ max (z-gate R v) 0 := by
  by_cases hv : v ≤ 2*σ
  · have hg : gate R v = 0 := gate_eq_zero R v (by linarith) (by linarith)
    rw [hg, sub_zero, max_eq_left hz]
    nlinarith [mul_le_mul_of_nonneg_left (bumpB_bounds σ v).2 hz]
  · rw [bumpB_zero σ v hσ (by linarith), mul_zero]
    exact le_max_right _ _

theorem weighted_bumpA (σ R v z : ℝ) (hR : 0 < R) (hz : 0 ≤ z) :
    z*bumpA σ R v ≤ max (z-gate R v) 0 := by
  by_cases hv : v ≤ 2*R
  · have hg : gate R v = 0 := gate_eq_zero R v hR (by linarith)
    rw [hg, sub_zero, max_eq_left hz]
    nlinarith [mul_le_mul_of_nonneg_left (bumpA_bounds σ R v hR).2 hz]
  · rw [bumpA_zero σ R v hR (by linarith), mul_zero]
    exact le_max_right _ _

theorem weighted_bumpB_sum (r σ R : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (z : X → ℝ) (hz : feasible r σ R z) (p : X) :
    (∑ s, z s*bumpB σ (dist s p/r)) ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun s _ => mul_nonneg (hz.1 s) (bumpB_bounds σ _).1
  · exact (Finset.sum_le_sum fun s _ => weighted_bumpB σ R _ _ hσ hσ1 hR (hz.1 s)).trans (hz.2.1 p)

theorem surcharge_sum (r σ R : ℝ) (hR : 0 < R) (g z : X → ℝ)
    (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z) (p : X) :
    (∑ s, z s*(1+g s)*bumpA σ R (dist s p/r)) ∈ Set.Icc (0:ℝ) 2 := by
  have hsum : (∑ s, z s*bumpA σ R (dist s p/r)) ≤ 1 :=
    (Finset.sum_le_sum fun s _ => weighted_bumpA σ R _ _ hR (hz.1 s)).trans (hz.2.1 p)
  constructor
  · apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (bumpA_bounds σ R _ hR).1
  · calc
      _ ≤ ∑ s, 2*(z s*bumpA σ R (dist s p/r)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hnn := mul_nonneg (hz.1 s) (bumpA_bounds σ R (dist s p/r) hR).1
        have hm := mul_le_mul_of_nonneg_left (show 1+g s ≤ 2 by linarith [(hg s).2]) hnn
        convert hm using 1 <;> ring
      _ = 2*∑ s, z s*bumpA σ R (dist s p/r) := (Finset.mul_sum ..).symm
      _ ≤ 2 := by linarith

theorem integrand_bounds (r σ R : ℝ) (_hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (g z : X → ℝ)
    (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z) (p : X) :
    integrand r σ R g z p ∈ Set.Icc (0:ℝ) 514 := by
  have hB := weighted_bumpB_sum r σ R hσ hσ1 hR z hz p
  have hA := surcharge_sum r σ R (by linarith) g z hg hz p
  have hn : 0 ≤ (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) :=
    mul_nonneg (by linarith [(hg p).1]) (by linarith [hB.2])
  have hu : (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) ≤ 2 := by
    have hh := mul_le_mul (show 1+g p ≤ 2 by linarith [(hg p).2])
      (show 1-∑ s, z s*bumpB σ (dist s p/r) ≤ 1 by linarith [hB.1])
      (show 0 ≤ 1-∑ s, z s*bumpB σ (dist s p/r) by linarith [hB.2]) (by norm_num : (0:ℝ) ≤ 2)
    simpa using hh
  unfold integrand
  constructor <;> linarith [hA.1, hA.2]

theorem value_bounds (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (μ g : X → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ value r σ R μ g ∧ value r σ R μ g ≤ 2*r*∑ p, μ p := by
  obtain ⟨z, hz, he, hmin⟩ := minimum_exists r σ R μ g
  constructor
  · rw [← he]
    apply mul_nonneg hr.le
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (hμ p) (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz p).1
  · have h0 := value_le r σ R μ g (fun _ => 0) (zero_feasible r σ R)
    have hb : objective r σ R μ g (fun _ => 0) ≤ 2*r*∑ p, μ p := by
      simp only [objective, integrand, zero_mul, Finset.sum_const_zero, sub_zero, mul_one, mul_zero,
        add_zero]
      calc
        _ ≤ r*∑ p, 2*μ p := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          apply Finset.sum_le_sum
          intro p hp
          nlinarith [mul_le_mul_of_nonneg_left (hg p).2 (hμ p)]
        _ = _ := by rw [← Finset.mul_sum]; ring
    exact h0.trans hb

theorem objective_linear (r σ R a b : ℝ) (μ ν g z : X → ℝ) :
    objective r σ R (fun p => a*μ p+b*ν p) g z =
      a*objective r σ R μ g z+b*objective r σ R ν g z := by
  unfold objective
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem value_concave (r σ R : ℝ) (g : X → ℝ) :
    ConcaveOn ℝ Set.univ (fun μ : X → ℝ => value r σ R μ g) := by
  refine ⟨convex_univ, ?_⟩
  intro μ hμ ν hν a b ha hb hab
  obtain ⟨z, hz, he, hmin⟩ := minimum_exists r σ R (a • μ + b • ν) g
  dsimp only
  rw [← he]
  change a*value r σ R μ g+b*value r σ R ν g ≤
    objective r σ R (fun p => a*μ p+b*ν p) g z
  rw [objective_linear]
  exact add_le_add (mul_le_mul_of_nonneg_left (value_le r σ R μ g z hz) ha)
    (mul_le_mul_of_nonneg_left (value_le r σ R ν g z hz) hb)

theorem candidate_drift [DecidableEq X] (r σ R : ℝ) (hr : 0 < r)
    (μ ν g : X → ℝ) (hν : ∀ p, 0 ≤ ν p) (hν1 : ∑ p, ν p = 1) (x : X)
    (z : X → ℝ) (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    value r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g - value r σ R μ g ≤
      r*∑ p, ν p*max (integrand r σ R g z x-integrand r σ R g z p) 0 := by
  have he : objective r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g z -
      objective r σ R μ g z = r*∑ p, ν p*(integrand r σ R g z x-integrand r σ R g z p) := by
    unfold objective
    simp_rw [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_sub, Finset.sum_sub_distrib]
    have hd : (∑ p : X, (if p=x then (1:ℝ) else 0)*integrand r σ R g z p) =
        integrand r σ R g z x := by simp
    rw [hd, ← Finset.sum_mul, hν1]
    ring
  calc
    _ ≤ objective r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g z -
        objective r σ R μ g z := by
      rw [hmin]
      exact sub_le_sub_right (value_le r σ R _ g z hz) _
    _ = _ := he
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hν p)


/-! Local optimality construction. -/
def ballMass (r a : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if dist x p ≤ a*r then μ p else 0

theorem feasible_mono (r σ R : ℝ) (z w : X → ℝ) (hz : feasible r σ R z)
    (hw : ∀ s, 0 ≤ w s) (hwz : ∀ s, w s ≤ z s) : feasible r σ R w := by
  refine ⟨hw, ?_, ?_⟩
  · intro p
    exact (Finset.sum_le_sum fun s _ => max_le_max (sub_le_sub_right (hwz s) _) le_rfl).trans (hz.2.1 p)
  · intro s s' hne hp hp'
    exact hz.2.2 s s' hne (hp.trans_le (hwz s)) (hp'.trans_le (hwz s'))

theorem erase_feasible [DecidableEq X] (r σ R : ℝ) (z : X → ℝ)
    (hz : feasible r σ R z) (s : X) : feasible r σ R (Function.update z s 0) := by
  apply feasible_mono r σ R z _ hz
  · intro p
    by_cases h : p=s <;> simp [h, hz.1 p]
  · intro p
    by_cases h : p=s <;> simp [h, hz.1 s]

def coefficient (r σ R : ℝ) (g : X → ℝ) (s p : X) : ℝ :=
  256*(1+g s)*bumpA σ R (dist s p/r) - (1+g p)*bumpB σ (dist s p/r)

omit [MetricSpace X] in
theorem sum_erase_weight [DecidableEq X] (z f : X → ℝ) (s : X) :
    (∑ t, z t*f t) - (∑ t, Function.update z s 0 t*f t) = z s*f s := by
  have he : ∀ t, z t*f t-Function.update z s 0 t*f t = if t=s then z s*f s else 0 := by
    intro t
    by_cases h : t=s <;> simp [h]
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  simp

theorem integrand_erase [DecidableEq X] (r σ R : ℝ) (g z : X → ℝ) (s p : X) :
    integrand r σ R g z p - integrand r σ R g (Function.update z s 0) p =
      z s*coefficient r σ R g s p := by
  have hb := sum_erase_weight z (fun t => bumpB σ (dist t p/r)) s
  have ha := sum_erase_weight z (fun t => (1+g t)*bumpA σ R (dist t p/r)) s
  simp only [← mul_assoc] at ha
  have hb' := congrArg (fun u : ℝ => (1+g p)*u) hb
  unfold integrand coefficient
  nlinarith only [hb', ha]


end
end UniformKServer.PilotCompact
end

end OAI
