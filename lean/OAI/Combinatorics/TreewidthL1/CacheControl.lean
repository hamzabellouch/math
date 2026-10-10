import OAI.Combinatorics.TreewidthL1.YoungestCrossing

namespace OAI

namespace BoundedTreewidthL1
open AnchorCache
attribute [local instance] Classical.decEq Classical.propDecidable
theorem near_far_scaled {V : Type*} [MetricSpace V]
    (B : Finset V) (x p v₀ : V) (h φ : V → ℝ)
    (δ D R a : ℝ) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hp : dist x p = δ) (hv : v₀ ∈ B)
    (hnear : ∀ s ∈ B, δ ≤ dist x s)
    (hh : ∀ u v, |h u - h v| ≤ dist u v)
    (hheight : h x = D) (hgeo : h v₀ + dist x v₀ = D)
    (hhnonneg : 0 ≤ h v₀)
    (hno : ∀ q ∈ B, ¬(δ/4 ≤ dist p q ∧ dist p q ≤ 10*D))
    (hR : R < 9*D) (ha : 0 < a) (hφx : a ≤ φ x)
    (hφ : ∀ s, R < dist x s → φ s = 0) :
    ∀ s ∈ B, δ/2 ≤ |h x-h s| ∨ a ≤ |φ x-φ s| := by
  have hvdist : dist p v₀ ≤ 2*D := by
    have ht := dist_triangle p x v₀
    rw [dist_comm p x, hp] at ht
    linarith
  have hvclose : dist p v₀ < δ/4 := by
    by_contra hn
    exact hno v₀ hv ⟨le_of_not_gt hn, by linarith⟩
  intro s hs
  by_cases hsclose : dist p s < δ/4
  · left
    have hvs : dist v₀ s < δ/2 := by
      have ht := dist_triangle v₀ p s
      rw [dist_comm v₀ p] at ht
      linarith
    have hhvs := (abs_le.mp (hh v₀ s)).1
    have hmin := hnear v₀ hv
    have hgap : δ/2 ≤ h x - h s := by rw [hheight]; linarith
    exact hgap.trans (le_abs_self _)
  · right
    have hfar : 10*D < dist p s := by
      by_contra hn
      exact hno s hs ⟨le_of_not_gt hsclose, le_of_not_gt hn⟩
    have hxs : R < dist x s := by
      have ht := dist_triangle p x s
      rw [dist_comm p x, hp] at ht
      linarith
    rw [hφ s hxs, sub_zero, abs_of_nonneg (ha.le.trans hφx)]
    exact hφx

lemma protected_threshold_scaled (K J H D₀ δ A L older younger : ℝ)
    (hK : 2 < K) (hJ : J = 10*(K+1)) (hH : 10^5*J < H)
    (hA : 0 < A) (hD : H*A < D₀) (hδ : 0 < δ) (_ : δ ≤ A)
    (hLlo : δ/4 ≤ L) (hLhi : L ≤ 10*D₀)
    (hyδ : younger ≤ K*δ) (hy2 : younger ≤ 2*A) (holder : D₀-A ≤ older) :
    ∃ τ ∈ ({L/100,J*L} : Set ℝ), younger ≤ τ ∧ τ < older := by
  have hJpos : 0 < J := by linarith
  have hHA : 10^5*J*A < H*A := mul_lt_mul_of_pos_right hH hA
  by_cases hL : L ≤ 300*A
  · refine ⟨J*L,by simp,?_,?_⟩
    · have hmul := mul_le_mul_of_nonneg_left hLlo hJpos.le
      have hgap : K*δ < J*(δ/4) := by rw [hJ]; nlinarith
      exact hyδ.trans (hgap.le.trans hmul)
    · have hmul := mul_le_mul_of_nonneg_left hL hJpos.le
      have hJA : 30*A < J*A := mul_lt_mul_of_pos_right (by linarith) hA
      norm_num at hHA
      nlinarith
  · refine ⟨L/100,by simp,by linarith,?_⟩
    have hJA : 30*A < J*A := mul_lt_mul_of_pos_right (by linarith) hA
    norm_num at hHA
    nlinarith

lemma protected_of_successor {V : Type*} [DecidableEq V]
    (R : ReservationPath) (B : Finset V) (D : V → ℕ → ℝ) (d : V → V → ℝ) (J : ℝ)
    (t a b : ℕ) (ht : t ≤ R.last) (hab : R.Successor a b t)
    (p q : V) (hp : p ∈ B) (hq : q ∈ B) (hpq : p ≠ q)
    (hw : ∃ τ ∈ ({d p q/100,J*d p q} : Set ℝ), D p b ≤ τ ∧ τ < D p a) :
    b ∈ protectedEntries B (R.inclusive t) d D J := by
  classical
  obtain ⟨τ,hτ,hlo,hhi⟩ := hw
  have hd : Drop (R.inclusive t) (D p) τ b := by
    refine ⟨(R.mem_inclusive ht).mpr hab.2.1,hlo,a,(R.mem_inclusive ht).mpr hab.1,hab.2.2.1,hhi,?_⟩
    intro c hc hac
    exact hab.2.2.2 c ((R.mem_inclusive ht).mp hc) hac
  apply Finset.mem_biUnion.mpr
  refine ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,?_⟩
  simp only [ite_eq_right hpq]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl
  · exact Finset.mem_biUnion.mpr ⟨false,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hd.1,hd⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨true,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hd.1,hd⟩⟩

/-- Physical, unnormalized data for a single actual root-to-endpoint cache.
The probabilistic tests are discharged from the constructed ensemble below. -/
structure GeometricTrack (V : Type*) [MetricSpace V] (N : ℕ) (U J H Q : ℝ) where
  path : ReservationPath
  start : ℕ
  start_le : start ≤ path.last
  delta : ℕ → ℝ
  antitone : Antitone delta
  nonneg : ∀ t, 0 ≤ delta t
  start_pos : 0 < delta start
  end_zero : delta path.last = 0
  error : ℝ
  error_nonneg : 0 ≤ error
  size : ∀ t, (path.inclusive t).card ≤ N
  B : ℕ → Finset V
  D : ℕ → V → ℝ
  x : V
  at_x : ∀ t, D t x = delta t
  lipschitz : ∀ a u v, |D a u-D a v| ≤ dist u v
  launch : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → start ≤ a →
    delta a ≤ error+(U+1)*delta e
  small : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → a < start →
    delta a ≤ H*delta start → delta start ≤ Q*(error+delta e)
  obstruction : ∀ a e t, e ≤ path.last → a ∈ path.inclusive e → a < start →
    start ≤ t → t < e → Q*(error+delta e) < delta t →
    ∃ p ∈ B t, ∃ q ∈ B t, dist x p = delta t ∧ delta t/4 ≤ dist p q ∧ dist p q ≤ 10*delta a
  protect_rule : ∀ t, t < path.last → ∀ b ∈ protectedEntries (B t) (path.inclusive t) dist
    (fun p a => D a p) J, t < path.finish b

namespace GeometricTrack
variable {V : Type*} [MetricSpace V] {N : ℕ} {U J H Q : ℝ}
  (P : GeometricTrack V N U J H Q)

lemma successor_protected (hU : 0 ≤ U) (hJ : J = 10*(U+4)) (hH : 10^5*J < H) (hQ : U+1 ≤ Q)
    (a e t b : ℕ) (he : e ≤ P.path.last) (ha : a ∈ P.path.inclusive e) (has : a < P.start)
    (hDa : H*P.delta P.start < P.delta a) (hst : P.start ≤ t) (hte : t < e)
    (hsb : P.start ≤ b) (hab : P.path.Successor a b t)
    (hgap : Q*(P.error+P.delta e) < P.delta t) : t < P.path.finish b := by
  classical
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hδ : 0 < P.delta t := lt_of_le_of_lt (mul_nonneg hQ0.le (add_nonneg P.error_nonneg (P.nonneg e))) hgap
  have hE : P.error < P.delta t := by
    have h1 := mul_le_mul_of_nonneg_right hQ1 (add_nonneg P.error_nonneg (P.nonneg e))
    nlinarith [P.nonneg e]
  obtain ⟨p,hp,q,hq,hxp,hLlo,hLhi⟩ := P.obstruction a e t he ha has hst hte hgap
  have hδA : P.delta t ≤ P.delta P.start := P.antitone hst
  have hdb : P.delta b ≤ P.delta P.start := P.antitone hsb
  have hbt : b ∈ P.path.inclusive t := (P.path.mem_inclusive (hte.le.trans he)).mpr hab.2.1
  have hl := P.launch b t (hte.le.trans he) hbt hsb
  have hbp := P.lipschitz b P.x p
  have hap := P.lipschitz a P.x p
  rw [P.at_x,hxp] at hbp hap
  have hbp' := (abs_le.mp hbp).1
  have hap' := (abs_le.mp hap).2
  have hyδ : P.D b p ≤ (U+3)*P.delta t := by nlinarith
  have hyA : P.D b p ≤ 2*P.delta P.start := by linarith
  have haA : P.delta a-P.delta P.start ≤ P.D a p := by linarith
  have hw := protected_threshold_scaled (U+3) J H (P.delta a) (P.delta t) (P.delta P.start)
    (dist p q) (P.D a p) (P.D b p) (by linarith) (by linarith) hH
    P.start_pos hDa hδ hδA hLlo hLhi hyδ hyA haA
  apply P.protect_rule t (hte.trans_le he) b
  apply protected_of_successor P.path (P.B t) (fun p a => P.D a p) dist J t a b
    (hte.le.trans he) hab p q hp hq _ hw
  intro heq; subst q; rw [dist_self] at hLlo; linarith

noncomputable def control (hU : 0 ≤ U) (hJ : J = 10*(U+4)) (hH : 10^5*J < H) (hQ : U+1 ≤ Q) :
    CacheControl N Q H where
  path := P.path
  start := P.start
  start_le := P.start_le
  delta := fun t => P.delta t/P.delta P.start
  antitone := fun _ _ h => div_le_div_of_nonneg_right (P.antitone h) P.start_pos.le
  nonneg := fun t => div_nonneg (P.nonneg t) P.start_pos.le
  at_start := div_self P.start_pos.ne'
  at_end := by rw [P.end_zero,zero_div]
  error := P.error/P.delta P.start
  error_nonneg := div_nonneg P.error_nonneg P.start_pos.le
  size := P.size
  launch := by
    intro a e he ha hs
    have hh := P.launch a e he ha hs
    have hq1 : 1 ≤ Q := by linarith
    have hb : P.error+(U+1)*P.delta e ≤ Q*(P.error+P.delta e) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1) P.error_nonneg,
        mul_nonneg (sub_nonneg.mpr hQ) (P.nonneg e)]
    have hd := div_le_div_of_nonneg_right (hh.trans hb) P.start_pos.le
    simpa only [mul_div_assoc,add_div] using hd
  distant := by
    intro a e he ha hs hd
    have hd' : P.delta a ≤ H*P.delta P.start := (div_le_iff₀ P.start_pos).mp hd
    have hh := div_le_div_of_nonneg_right (P.small a e he ha hs hd') P.start_pos.le
    rw [div_self P.start_pos.ne'] at hh
    simpa only [mul_div_assoc,add_div] using hh
  protect := by
    intro a e t b he ha hs hd hst hte hsb hab hgap
    have hd' : H*P.delta P.start < P.delta a := (lt_div_iff₀ P.start_pos).mp hd
    have hg : Q*(P.error+P.delta e) < P.delta t := by
      apply (div_lt_div_iff_of_pos_right P.start_pos).mp
      simpa only [mul_div_assoc,add_div] using hgap
    exact P.successor_protected hU hJ hH hQ a e t b he ha hs hd' hst hte hsb hab hg

end GeometricTrack
end BoundedTreewidthL1

end OAI
