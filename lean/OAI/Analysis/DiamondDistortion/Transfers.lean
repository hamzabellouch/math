import OAI.Analysis.DiamondDistortion.MidpointHeads

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem quotient_full_gain {t g D s : ℝ} (ht : 0 < t) (hg : 0 < g)
    (htD : t ≤ 1/(2*D)) (hX : Midpoint.QuotientGain X t g)
    (k : ℕ) (f : Vertex k → X) (hf : HasDistortion k f D s) :
    1 ≤ D/(1+g)^k := by
  obtain ⟨hD,_,h⟩ := normalized_distortion f hf
  have hg1 : 0 < 1+g := by positivity
  let c : ℝ := 1/(1+g)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one₀ hg1).mpr (by linarith)
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ c*R := by
    intro x z R hR hRD hx hp hm hs
    have hxD := (norm_center_le (hp 0) (hm 0)).trans hRD
    have h := Midpoint.quotient_parent_full_gain ht hg hD htD hX z hx hxD hp hm
      (by simpa only [mul_one] using hs)
    simpa only [c,div_eq_mul_inv,one_mul,mul_comm] using h
  have hi := iterate_contraction hc hc1 hstep k (fun v => s⁻¹ • f v)
    (show 0 ≤ D by linarith) le_rfl (fun u v => by simpa only [one_mul] using (h u v).1)
    (fun e => slope_upper _ (fun u v => by simpa only [mul_one] using (h u v).2) e)
  simpa only [c,div_pow,one_pow,div_eq_mul_inv,one_mul,mul_comm,inv_pow] using hi

theorem quotient_transfer {t g D s : ℝ} (ht : 0 < t) (hg : 0 < g)
    (htD : t ≤ 1/(2*D)) (hX : Midpoint.QuotientGain X t g)
    (k : ℕ) (f : Vertex k → X) (hf : HasDistortion k f D s) :
    (1+g/2)^k ≤ D := by
  have h := quotient_full_gain ht hg htD hX k f hf
  have hp : 0 < (1+g)^k := by positivity
  have hpow : (1+g)^k ≤ D := by simpa only [one_mul] using (le_div_iff₀ hp).mp h
  exact (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+g/2) (by linarith : 1+g/2 ≤ 1+g) k).trans hpow

/-- A parent at any of the k replacement stages, with all of its actual children
    bounded by the specified multiple of its own slope. The recursion restricts
    to old vertices and therefore includes every stage, not just the last one. -/
def StableParent (c : ℝ) : (k : ℕ) → (Vertex k → X) → Prop
  | 0,_ => False
  | n+1,f => (∃ e : Edge n,∀ (i : ℕ) (b : Bool),
      ‖slope f (e,i,b)‖ ≤ c*‖slope (fun v => f (Sum.inl v)) e‖) ∨
      StableParent c n (fun v => f (Sum.inl v))

lemma absence_stable_growth {c s : ℝ} (hc : 0 ≤ c) (k : ℕ) (f : Vertex k → X)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖) (hn : ¬ StableParent c k f) :
    ∃ e : Edge k,s*c^k ≤ ‖slope f e‖ := by
  induction k with
  | zero => exact ⟨(),by simpa using slope_lower f hl ()⟩
  | succ n ih =>
    simp only [StableParent,not_or] at hn
    obtain ⟨e,he⟩ := ih (fun v => f (Sum.inl v)) (old_lower f hl) hn.2
    have hne : ¬ ∀ (i : ℕ) (b : Bool),
        ‖slope f (e,i,b)‖ ≤ c*‖slope (fun v => f (Sum.inl v)) e‖ :=
      fun h => hn.1 ⟨e,h⟩
    push Not at hne
    obtain ⟨i,b,hchild⟩ := hne
    refine ⟨(e,i,b),?_⟩
    have hm := mul_le_mul_of_nonneg_left he hc
    calc
      s*c^(n+1) = c*(s*c^n) := by ring
      _ ≤ c*‖slope (fun v => f (Sum.inl v)) e‖ := hm
      _ ≤ ‖slope f (e,i,b)‖ := hchild.le

theorem stable_parent {D δ : ℝ} (hδ : 0 < δ) (k : ℕ) (f : Vertex k → X)
    (hf : HasDistortion k f D 1) (hdepth : D < (1+δ)^k) :
    StableParent (1+δ) k f := by
  by_contra hn
  obtain ⟨e,he⟩ := absence_stable_growth (by positivity : 0 ≤ 1+δ) k f
    (fun u v => (hf.2.2 u v).1) hn
  have hb : ‖slope f e‖ ≤ D := slope_upper f
    (fun u v => by simpa only [mul_one] using (hf.2.2 u v).2) e
  simp only [one_mul] at he
  linarith

/-- Exact exclusion of infinite separated families in every enlarged unit-center
    lens, retaining the radius and separation as independent parameters. -/
def EnlargedLensExcluded (X : Type*) [NormedAddCommGroup X] (R β : ℝ) : Prop :=
  ∀ u : X,‖u‖=1 → ¬ ∃ z : ℕ → X,
    (∀ i,max ‖u+z i‖ ‖u-z i‖ ≤ 1+β) ∧
    (∀ i j,i ≠ j → R ≤ ‖z i-z j‖)

lemma enlarged_parent {D β L : ℝ} (_hD : 1 ≤ D) (hβ : 0 < β)
    (hX : EnlargedLensExcluded X (2/D) β) {x : X} (z : ℕ → X)
    (hx : 1 ≤ ‖x‖) (hxD : ‖x‖ ≤ D)
    (hp : ∀ i,‖x+z i‖ ≤ L) (hm : ∀ i,‖x-z i‖ ≤ L)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) : ‖x‖ < L/(1+β) := by
  by_contra! hn
  let r := ‖x‖
  have hr : 0 < r := by dsimp [r]; linarith
  have hβ1 : 0 < 1+β := by positivity
  have hL : L ≤ r*(1+β) := (div_le_iff₀ hβ1).mp hn
  have hunit : ‖r⁻¹ • x‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),inv_mul_cancel₀ hr.ne']
  apply hX (r⁻¹ • x) hunit
  refine ⟨fun i => r⁻¹ • z i,?_,?_⟩
  · intro i
    apply max_le
    · rw [← smul_add,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      calc
        r⁻¹*‖x+z i‖ ≤ r⁻¹*(r*(1+β)) :=
          mul_le_mul_of_nonneg_left ((hp i).trans hL) (inv_nonneg.mpr hr.le)
        _ = 1+β := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    · rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      calc
        r⁻¹*‖x-z i‖ ≤ r⁻¹*(r*(1+β)) :=
          mul_le_mul_of_nonneg_left ((hm i).trans hL) (inv_nonneg.mpr hr.le)
        _ = 1+β := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
  · intro i j hij
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      2/D ≤ 2/r := div_le_div_of_nonneg_left (by norm_num) hr hxD
      _ = r⁻¹*2 := by ring
      _ ≤ r⁻¹*‖z i-z j‖ := mul_le_mul_of_nonneg_left (hs i j hij) (inv_nonneg.mpr hr.le)

theorem enlarged_backward {D β s : ℝ} (hβ : 0 < β)
    (hX : EnlargedLensExcluded X (2/D) β) (k : ℕ) (f : Vertex k → X)
    (hf : HasDistortion k f D s) : 1 ≤ D/(1+β)^k := by
  obtain ⟨hD,_,h⟩ := normalized_distortion f hf
  have hβ1 : 0 < 1+β := by positivity
  let c : ℝ := 1/(1+β)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one₀ hβ1).mpr (by linarith)
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ c*R := by
    intro x z R hR hRD hx hp hm hs
    have hxD := (norm_center_le (hp 0) (hm 0)).trans hRD
    have h := (enlarged_parent hD hβ hX z hx hxD hp hm
      (by simpa only [mul_one] using hs)).le
    simpa only [c,div_eq_mul_inv,one_mul,mul_comm] using h
  have hi := iterate_contraction hc hc1 hstep k (fun v => s⁻¹ • f v)
    (show 0 ≤ D by linarith) le_rfl (fun u v => by simpa only [one_mul] using (h u v).1)
    (fun e => slope_upper _ (fun u v => by simpa only [mul_one] using (h u v).2) e)
  simpa only [c,div_pow,one_pow,div_eq_mul_inv,one_mul,mul_comm,inv_pow] using hi

theorem stable_parent_obstruction {D δ s : ℝ} (hδ : 0 < δ)
    (hX : EnlargedLensExcluded X (2/D) δ) (k : ℕ) (f : Vertex k → X)
    (hf : HasDistortion k f D s) : (1+δ)^k ≤ D := by
  have h := enlarged_backward hδ hX k f hf
  simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < (1+δ)^k)).mp h

end

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Supremum of all edge slopes at one stage; not a maximum. -/
def stageSup {k : ℕ} (f : Vertex k → X) : ℝ :=
  sSup (Set.range (fun e : Edge k => ‖slope f e‖))

lemma slope_le_stageSup {k : ℕ} (f : Vertex k → X) {D : ℝ}
    (hb : ∀ e,‖slope f e‖ ≤ D) (e : Edge k) : ‖slope f e‖ ≤ stageSup f := by
  exact le_csSup ⟨D,by rintro _ ⟨e,rfl⟩; exact hb e⟩ ⟨e,rfl⟩

lemma stageSup_le {k : ℕ} (f : Vertex k → X) {D : ℝ}
    (hb : ∀ e,‖slope f e‖ ≤ D) : stageSup f ≤ D := by
  unfold stageSup
  apply csSup_le (s := Set.range (fun e : Edge k => ‖slope f e‖))
    ⟨‖slope f (baseEdge k)‖,⟨baseEdge k,rfl⟩⟩
  rintro _ ⟨e,rfl⟩
  exact hb e

lemma parametric_Q_one {b lam : ℝ} (hb : 0 < b) : 1 ≤ Real.sqrt (1+b*lam^2) := by
  have h : (1:ℝ)^2 ≤ 1+b*lam^2 := by nlinarith [mul_nonneg hb.le (sq_nonneg lam)]
  exact (Real.le_sqrt (by norm_num) (by positivity)).mpr h

theorem parametric_stage (A : Midpoint.Heads ι X) {a b lam D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam) (hinput : A.ParametricInput a b)
    (n : ℕ) (f : Vertex (n+1) → X) (hf : HasDistortion (n+1) f D 1) :
    let Q := Real.sqrt (1+b*lam^2)
    stageSup (fun v => f (Sum.inl v)) ≤ Q*stageSup f-a*lam ∧
    Q*stageSup f-a*lam ≤ stageSup f-(a*lam-(Q-1)*D) := by
  let Q := Real.sqrt (1+b*lam^2)
  have hbnd : ∀ e,‖slope f e‖ ≤ D := slope_upper f
    (fun u v => by simpa only [mul_one] using (hf.2.2 u v).2)
  have hR : stageSup f ≤ D := stageSup_le f hbnd
  have hQ : 1 ≤ Q := parametric_Q_one hb
  constructor
  · apply stageSup_le
    intro e
    have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ stageSup f := by
      intro i
      rw [slope_plus_deviation]
      exact slope_le_stageSup f hbnd _
    have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ stageSup f := by
      intro i
      rw [slope_minus_deviation]
      exact slope_le_stageSup f hbnd _
    have hs : ∀ i j,i ≠ j → 2 ≤ ‖deviation f e i-deviation f e j‖ := by
      intro i j hij
      simpa only [mul_one] using deviation_separated f (fun u v => (hf.2.2 u v).1) e hij
    have h := A.parametric_lens ha hb hlam hinput (deviation f e) hp hm hs
    norm_num at h
    linarith
  · change Q*stageSup f-a*lam ≤ stageSup f-(a*lam-(Q-1)*D)
    nlinarith [mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hQ)]

/-- The exact parameterized graph depth conclusion; no optimization performed. -/
theorem parametric (A : Midpoint.Heads ι X) {a b lam D s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam) (hinput : A.ParametricInput a b)
    (hΔ : 0 < a*lam-(Real.sqrt (1+b*lam^2)-1)*D)
    (k : ℕ) (f : Vertex k → X) (hf : HasDistortion k f D s) :
    1+(k:ℝ)*(a*lam-(Real.sqrt (1+b*lam^2)-1)*D) ≤ D := by
  obtain ⟨hD,_,h⟩ := normalized_distortion f hf
  let Q := Real.sqrt (1+b*lam^2)
  let δ := a*lam-(Q-1)*D
  have hQ : 1 ≤ Q := parametric_Q_one hb
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ R-δ := by
    intro x z R hR hRD hx hp hm hs
    have hh := A.parametric_lens ha hb hlam hinput z hp hm hs
    norm_num at hh
    dsimp [δ]
    change ‖x‖+a*lam ≤ Q*R at hh
    nlinarith [mul_le_mul_of_nonneg_left hRD (sub_nonneg.mpr hQ)]
  exact iterate_additive hΔ.le hstep k (fun v => s⁻¹ • f v)
    (show 0 ≤ D by linarith) le_rfl (fun u v => by simpa only [one_mul] using (h u v).1)
    (fun e => slope_upper _ (fun u v => by simpa only [mul_one] using (h u v).2) e)

theorem parametric_twentyfour (A : Midpoint.Heads ι X) (hinput : A.ParametricInput (1/2) 3)
    {D s : ℝ} (k : ℕ) (f : Vertex k → X) (hf : HasDistortion k f D s) :
    1+(k:ℝ)/(24*D) ≤ D := by
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf.1
  let lam := 1/(6*D)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hQ : Real.sqrt (1+3*lam^2) ≤ 1+3*lam^2/2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [sq_nonneg (3*lam^2/2)]
  have hden : (6*D) ≠ 0 := by positivity
  have hlD : lam*(6*D)=1 := by dsimp [lam]; field_simp
  have hgain : 1/(24*D) ≤ (1/2)*lam-(Real.sqrt (1+3*lam^2)-1)*D := by
    have hs := mul_le_mul_of_nonneg_right hQ hD.le
    have he : (1/2)*lam-(3*lam^2/2)*D = 1/(24*D) := by
      dsimp [lam]
      field_simp
      ring
    linarith
  have hΔ : 0 < (1/2)*lam-(Real.sqrt (1+3*lam^2)-1)*D :=
    lt_of_lt_of_le (by positivity) hgain
  have h := parametric A (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<3) hlam hinput hΔ k f hf
  have hm := mul_le_mul_of_nonneg_left hgain (show 0 ≤ (k:ℝ) by positivity)
  have he : (k:ℝ)/(24*D)=(k:ℝ)*(1/(24*D)) := by ring
  linarith

end Diamond

end DiamondDistortion

end

end OAI
