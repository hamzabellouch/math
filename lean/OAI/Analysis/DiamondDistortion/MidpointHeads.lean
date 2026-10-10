import OAI.Analysis.DiamondDistortion.Stretch

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Midpoint

section
variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- An actual family of allowed finite-rank coordinate heads. Approximation is
    by a vector fixed by a head; no uniform bound on projection norms is imposed. -/
structure Heads (ι : Type*) (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  projection : ι → X →L[ℝ] X
  idempotent : ∀ H x,projection H (projection H x)=projection H x
  finite : ∀ H,FiniteDimensional ℝ (LinearMap.range (projection H).toLinearMap)
  approximation : ∀ (x : X) (η : ℝ),0 < η →
    ∃ (H : ι) (p : X),projection H p=p ∧ ‖x-p‖ < η

/-- Image compactness, with a finite-dimensional target and no assumption that
    a supremum over a sequence is attained. -/
lemma finite_dimensional_pair [FiniteDimensional ℝ Y] (P : X →L[ℝ] Y)
    (z : ℕ → X) {R η : ℝ} (hz : ∀ i,‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ,i ≠ j ∧ ‖P ((1/2:ℝ) • (z i-z j))‖ < η := by
  have hZ (i : ℕ) : P (z i) ∈ Metric.closedBall (0 : Y) (‖P‖*R) := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _))
  obtain ⟨a,_,φ,hφ,hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hZ
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (2*η) (by positivity)
  have hd := hN N le_rfl (N+1) (by omega)
  change dist (P (z (φ N))) (P (z (φ (N+1)))) < 2*η at hd
  rw [dist_eq_norm] at hd
  refine ⟨φ N,φ (N+1),hφ.injective.ne (by omega),?_⟩
  rw [map_smul,norm_smul,map_sub,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

lemma finite_rank_pair (P : X →L[ℝ] X)
    [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    (z : ℕ → X) {R η : ℝ} (hz : ∀ i,‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ,i ≠ j ∧ ‖P ((1/2:ℝ) • (z i-z j))‖ < η := by
  let Q : X →L[ℝ] (LinearMap.range P.toLinearMap) :=
    P.codRestrict _ (fun x => ⟨x,rfl⟩)
  exact finite_dimensional_pair Q z hz hη

lemma average_lens {x : X} (z : ℕ → X) {R : ℝ}
    (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R) (i j : ℕ) :
    ‖x+(1/2:ℝ) • (z i-z j)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (z i-z j)‖ ≤ R := by
  have he1 : x+(1/2:ℝ) • (z i-z j)=(1/2:ℝ) • ((x+z i)+(x-z j)) := by module
  have he2 : x-(1/2:ℝ) • (z i-z j)=(1/2:ℝ) • ((x-z i)+(x+z j)) := by module
  constructor
  · rw [he1,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x+z i) (x-z j)).trans (add_le_add (hp i) (hm j))
    linarith
  · rw [he2,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x-z i) (x+z j)).trans (add_le_add (hm i) (hp j))
    linarith

lemma pair_errors (P : X →L[ℝ] X)
    [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    {x p : X} (z : ℕ → X) {R ε η : ℝ} (hη : 0 < η)
    (hclose : ‖x-p‖ < η) (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R)
    (hs : ∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) :
    ∃ i j : ℕ,i ≠ j ∧
      let w := (1/2:ℝ) • (z i-z j)
      let y := w-P w
      ‖P w‖ < η ∧ ε/2-η ≤ ‖y‖ ∧ ‖x‖-η ≤ ‖p‖ ∧
        ‖p+y‖ ≤ R+2*η ∧ ‖p-y‖ ≤ R+2*η ∧ ‖x+w‖ ≤ R ∧ ‖x-w‖ ≤ R := by
  obtain ⟨i,j,hij,hP⟩ := finite_rank_pair P z
    (fun i => Diamond.norm_deviation_le (hp i) (hm i)) hη
  let w := (1/2:ℝ) • (z i-z j)
  have hw : ε/2 ≤ ‖w‖ := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith [hs i j hij]
  have hy : ε/2-η ≤ ‖w-P w‖ := by
    have h := norm_sub_norm_le w (P w)
    linarith
  have hpn : ‖x‖-η ≤ ‖p‖ := by linarith [norm_sub_norm_le x p]
  obtain ⟨ha,hb⟩ := average_lens z hp hm i j
  have hpp : ‖p+(w-P w)‖ ≤ R+2*η := by
    have he : p+(w-P w)=(x+w)-(x-p)-P w := by module
    rw [he]
    have h := (norm_sub_le ((x+w)-(x-p)) (P w)).trans
      (add_le_add (norm_sub_le (x+w) (x-p)) le_rfl)
    linarith
  have hpm : ‖p-(w-P w)‖ ≤ R+2*η := by
    have he : p-(w-P w)=(x-w)-(x-p)+P w := by module
    rw [he]
    have h := (norm_add_le ((x-w)-(x-p)) (P w)).trans
      (add_le_add (norm_sub_le (x-w) (x-p)) le_rfl)
    linarith
  exact ⟨i,j,hij,hP,hy,hpn,hpp,hpm,ha,hb⟩

/-- The quotient version chooses an actual nearby subspace vector, not just a
    formal quotient with small norm. Closedness and true finite codimension are explicit. -/
lemma quotient_pair (F : Submodule ℝ X) [IsClosed (F : Set X)]
    [FiniteDimensional ℝ (X ⧸ F)] (z : ℕ → X) {R η : ℝ}
    (hz : ∀ i,‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ (i j : ℕ) (v : X),i ≠ j ∧ v ∈ F ∧ ‖(1/2:ℝ) • (z i-z j)-v‖ < η := by
  obtain ⟨i,j,hij,hq⟩ := finite_dimensional_pair F.mkQL z hz (half_pos hη)
  let w := (1/2:ℝ) • (z i-z j)
  obtain ⟨m,hm,hn⟩ := Submodule.Quotient.norm_mk_lt (F.mkQL w) (half_pos hη)
  refine ⟨i,j,w-m,hij,?_,?_⟩
  · apply (Submodule.Quotient.mk_eq_zero F).mp
    change F.mkQ (w-m)=0
    rw [map_sub]
    change F.mkQL w-Submodule.Quotient.mk m=0
    rw [hm,sub_self]
  · rw [sub_sub_cancel]
    linarith

end

section
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma positive_limit_le (f g : ℝ → ℝ) (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (h : ∀ η,0 < η → f η ≤ g η) : f 0 ≤ g 0 := by
  have ht : Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto (hf.tendsto.comp ht) (hg.tendsto.comp ht)
    (Filter.Eventually.of_forall (fun n => h _ (by positivity)))

lemma Heads.pure_pair (A : Heads ι X) {x : X} (z : ℕ → X) {R ε η : ℝ} (hη : 0 < η)
    (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R)
    (hs : ∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) :
    ∃ (H : ι) (p y : X),A.projection H p=p ∧ A.projection H y=0 ∧
      ‖x‖-η ≤ ‖p‖ ∧ ε/2-η ≤ ‖y‖ ∧ ‖p+y‖ ≤ R+2*η ∧ ‖p-y‖ ≤ R+2*η := by
  obtain ⟨H,p,hP,hclose⟩ := A.approximation x η hη
  let := A.finite H
  obtain ⟨i,j,_,hpair⟩ := pair_errors (A.projection H) z hη hclose hp hm hs
  refine ⟨H,p,(1/2:ℝ) • (z i-z j)-A.projection H ((1/2:ℝ) • (z i-z j)),hP,?_,
    hpair.2.2.1,hpair.2.1,hpair.2.2.2.1,hpair.2.2.2.2.1⟩
  rw [map_sub,A.idempotent,sub_self]

def Heads.SquareInput (A : Heads ι X) (a : ℝ) : Prop :=
  ∀ (H : ι) (p y : X) (R : ℝ),A.projection H p=p → A.projection H y=0 →
    0 ≤ R → ‖p+y‖ ≤ R → ‖p-y‖ ≤ R → ‖p‖^2+a*‖y‖^2 ≤ R^2

def Heads.RadialInput (A : Heads ι X) (C : ℝ) : Prop :=
  ∀ (H : ι) (p y : X) (R : ℝ),A.projection H p=p → A.projection H y=0 →
    0 ≤ R → ‖p+y‖ ≤ R → ‖p-y‖ ≤ R → ‖y‖^2 ≤ C^2*R*(R-‖p‖)

theorem Heads.square_lens (A : Heads ι X) {a : ℝ} (ha : 0 < a) (hinput : A.SquareInput a) :
    Diamond.SquareLens X (a/4) := by
  intro x z R ε hR hε hp hm hs
  have hh := positive_limit_le
    (fun η => (max (‖x‖-η) 0)^2+a*(max (ε/2-η) 0)^2)
    (fun η => (R+2*η)^2) (by fun_prop) (by fun_prop) (fun η hη => by
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hη hp hm hs
      have h := hinput H p y (R+2*η) hP hY (by positivity) hpR hmR
      have hp' : max (‖x‖-η) 0 ≤ ‖p‖ := max_le hpL (norm_nonneg _)
      have hy' : max (ε/2-η) 0 ≤ ‖y‖ := max_le hyL (norm_nonneg _)
      have hp2 := (sq_le_sq₀ (le_max_right _ _) (norm_nonneg _)).mpr hp'
      have hy2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (le_max_right _ _) (norm_nonneg _)).mpr hy') ha.le
      linarith)
  simp only [sub_zero,mul_zero,add_zero,max_eq_left (norm_nonneg x),
    max_eq_left (half_pos hε).le] at hh
  nlinarith only [hh]

theorem Heads.radial_lens (A : Heads ι X) {C : ℝ} (hC : 0 < C) (hinput : A.RadialInput C) :
    Diamond.RadialLens X C := by
  intro x z R ε hR hε hp hm hs
  have hh := positive_limit_le
    (fun η => (max (ε/2-η) 0)^2)
    (fun η => C^2*(R+2*η)*(R+3*η-‖x‖)) (by fun_prop) (by fun_prop) (fun η hη => by
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hη hp hm hs
      have h := hinput H p y (R+2*η) hP hY (by positivity) hpR hmR
      have hy' : max (ε/2-η) 0 ≤ ‖y‖ := max_le hyL (norm_nonneg _)
      have hy2 := (sq_le_sq₀ (le_max_right _ _) (norm_nonneg _)).mpr hy'
      have hmul := mul_le_mul_of_nonneg_left
        (show R+2*η-‖p‖ ≤ R+3*η-‖x‖ by linarith)
        (show 0 ≤ C^2*(R+2*η) by positivity)
      exact hy2.trans (h.trans hmul))
  simp only [sub_zero,mul_zero,add_zero,max_eq_left (half_pos hε).le] at hh
  nlinarith only [hh]

def Heads.ParametricInput (A : Heads ι X) (a b : ℝ) : Prop :=
  ∀ (H : ι) (p y : X) (lam : ℝ),A.projection H p=p → A.projection H y=0 → 0 < lam →
    (‖p‖+a*lam*‖y‖)/Real.sqrt (1+b*lam^2) ≤ max ‖p+y‖ ‖p-y‖

theorem Heads.parametric_lens (A : Heads ι X) {a b lam : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam) (hinput : A.ParametricInput a b)
    {x : X} (z : ℕ → X) {R ε : ℝ}
    (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R)
    (hs : ∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) :
    ‖x‖+a*lam*(ε/2) ≤ Real.sqrt (1+b*lam^2)*R := by
  let Q := Real.sqrt (1+b*lam^2)
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hh := positive_limit_le (fun _ => ‖x‖+a*lam*(ε/2))
    (fun η => Q*(R+2*η)+(1+a*lam)*η) (by fun_prop) (by fun_prop) (fun η hη => by
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hη hp hm hs
      have h := (hinput H p y lam hP hY hlam).trans (max_le hpR hmR)
      have h' : ‖p‖+a*lam*‖y‖ ≤ (R+2*η)*Q := (div_le_iff₀ hQ).mp h
      have hs := mul_le_mul_of_nonneg_left hyL (show 0 ≤ a*lam by positivity)
      nlinarith only [h',hs,hpL])
  simpa only [mul_zero,add_zero] using hh

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def QuotientGain (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (t g : ℝ) : Prop :=
  ∀ u : X,‖u‖=1 → ∃ F : Submodule ℝ X,IsClosed (F : Set X) ∧
    FiniteDimensional ℝ (X ⧸ F) ∧
    ∀ y : X,y ∈ F → t ≤ ‖y‖ → 1+g ≤ max ‖u+y‖ ‖u-y‖

lemma quotient_parent_full_gain {t g D L : ℝ} (ht : 0 < t) (hg : 0 < g)
    (hD : 1 ≤ D) (htD : t ≤ 1/(2*D)) (hX : QuotientGain X t g)
    {x : X} (z : ℕ → X) (hx : 1 ≤ ‖x‖) (hxD : ‖x‖ ≤ D)
    (hp : ∀ i,‖x+z i‖ ≤ L) (hm : ∀ i,‖x-z i‖ ≤ L)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) : ‖x‖ ≤ L/(1+g) := by
  let r := ‖x‖
  have hr : 0 < r := by dsimp [r]; linarith
  have hunit : ‖r⁻¹ • x‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),inv_mul_cancel₀ hr.ne']
  obtain ⟨F,hclosed,hfinite,hF⟩ := hX (r⁻¹ • x) hunit
  let := hclosed
  let := hfinite
  have hfull : r*(1+g) ≤ L := by
    apply le_of_forall_pos_le_add
    intro η hη
    let δ := min (1/2:ℝ) η
    have hδ : 0 < δ := lt_min (by norm_num) hη
    obtain ⟨i,j,v,hij,hvF,hclose⟩ := quotient_pair F z
      (fun i => Diamond.norm_deviation_le (hp i) (hm i)) hδ
    let w := (1/2:ℝ) • (z i-z j)
    have hw : 1 ≤ ‖w‖ := by
      dsimp [w]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      linarith [hs i j hij]
    have hv : (1/2:ℝ) ≤ ‖v‖ := by
      have h := norm_sub_norm_le w v
      have hδhalf : δ ≤ 1/2 := min_le_left _ _
      linarith
    have htr : t*r ≤ 1/2 := by
      have htd : t*(2*D) ≤ 1 := (le_div_iff₀ (by linarith : 0 < 2*D)).mp htD
      have hmul := mul_le_mul_of_nonneg_left hxD ht.le
      change t*r ≤ t*D at hmul
      nlinarith
    have htv : t ≤ ‖r⁻¹ • v‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      calc
        t = r⁻¹*(t*r) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (htr.trans hv) (inv_nonneg.mpr hr.le)
    obtain ⟨hwp,hwm⟩ := average_lens z hp hm i j
    have hδη : δ ≤ η := min_le_right _ _
    have hplus : ‖x+v‖ ≤ L+η := by
      have he : x+v=(x+w)-(w-v) := by module
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have hminus : ‖x-v‖ ≤ L+η := by
      have he : x-v=(x-w)+(w-v) := by module
      rw [he]
      exact (norm_add_le _ _).trans (by linarith)
    have hgain := hF (r⁻¹ • v) (F.smul_mem _ hvF) htv
    have hupper : max ‖r⁻¹ • x+r⁻¹ • v‖ ‖r⁻¹ • x-r⁻¹ • v‖ ≤ r⁻¹*(L+η) := by
      apply max_le
      · rw [← smul_add,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact mul_le_mul_of_nonneg_left hplus (inv_nonneg.mpr hr.le)
      · rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact mul_le_mul_of_nonneg_left hminus (inv_nonneg.mpr hr.le)
    have h := mul_le_mul_of_nonneg_left (hgain.trans hupper) hr.le
    rwa [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at h
  exact (le_div_iff₀ (by positivity : 0 < 1+g)).mpr hfull

/-- Approximate actual-child selection: the supremal full gain implies a
    strictly larger actual child at the half-gain threshold, never a maximum. -/
lemma quotient_actual_child {t g D : ℝ} (ht : 0 < t) (hg : 0 < g)
    (hD : 1 ≤ D) (htD : t ≤ 1/(2*D)) (hX : QuotientGain X t g)
    {x : X} (z : ℕ → X) (hx : 1 ≤ ‖x‖) (hxD : ‖x‖ ≤ D)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) :
    ∃ i,‖x‖*(1+g/2) < max ‖x+z i‖ ‖x-z i‖ := by
  by_contra! hn
  have hp : ∀ i,‖x+z i‖ ≤ ‖x‖*(1+g/2) := fun i => (le_max_left _ _).trans (hn i)
  have hm : ∀ i,‖x-z i‖ ≤ ‖x‖*(1+g/2) := fun i => (le_max_right _ _).trans (hn i)
  have h := quotient_parent_full_gain ht hg hD htD hX z hx hxD hp hm hs
  have h' := (le_div_iff₀ (by positivity : 0 < 1+g)).mp h
  nlinarith [mul_pos (show 0 < ‖x‖ by linarith) hg]

end Midpoint

end DiamondDistortion

end

end OAI
