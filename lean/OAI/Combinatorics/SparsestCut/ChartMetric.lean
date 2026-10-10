import OAI.Combinatorics.SparsestCut.TriangleRepair

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartMetric
open scoped BigOperators RealInnerProductSpace
open TriangleRepair
noncomputable section
variable {ι : Type u1} {C : Type u2} {J : Type u3} {E : Type u4} {H : Type u5} [Fintype ι] [Fintype C] [Fintype J] [DecidableEq C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma neg_min_eq (a b : ℝ) : -min a b=max (-a) (-b) := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_left (neg_le_neg h)]
  · rw [min_eq_right h,max_eq_right (neg_le_neg h)]

omit [Fintype ι] [Fintype C] [InnerProductSpace ℝ H] in
lemma capped_angle (c : ι → C) (h : ι → H) {r : ℝ} (P : ι → E)
    (hg : ∀ v z y, -r≤ inner ℝ (P v-P z) (P y-P z))
    (hl : ∀ v z y, c v=c z → |inner ℝ (P v-P z) (P y-P z)|≤‖h v-h z‖^2) :
    ∀ v y z, -min (cappedDistance c h r v z) (cappedDistance c h r y z)≤
      inner ℝ (P v-P z) (P y-P z) := by
  intro v y z
  have h1 : -cappedDistance c h r v z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c v=c z
    · have hh := (abs_le.mp (hl v z y hc)).1
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  have h2 : -cappedDistance c h r y z≤ inner ℝ (P v-P z) (P y-P z) := by
    by_cases hc : c y=c z
    · have hh := (abs_le.mp (hl y z v hc)).1
      rw [real_inner_comm] at hh
      simp only [cappedDistance,hc,ite_true,neg_min_eq]
      exact max_le (hg v z y) hh
    · simpa only [cappedDistance,hc,ite_false] using hg v z y
  rw [neg_min_eq]
  exact max_le h1 h2

omit [InnerProductSpace ℝ H] [Fintype C] in

lemma repair_from_angles (c : ι → C) (x : ι → J → ℝ) {L r : ℝ} (hL : 0≤L) (hr : 0<r)
    (P : ι → E) (θ : ι → H) {q e : ℝ}
    (hm : ∀ v w, |‖P v-P w‖^2-q*‖θ v-θ w‖|≤e)
    (hg : ∀ v z y, -r≤ inner ℝ (P v-P z) (P y-P z))
    (hl : ∀ v z y, c v=c z → |inner ℝ (P v-P z) (P y-P z)|≤L*∑ j, |x v j-x z j|) :
    ∃ Z : ι → EuclideanSpace ℝ ι,
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-q*‖θ v-θ w‖|≤e+8*r) ∧
      (∀ v w, c v=c w → 0<L*(∑ j, |x v j-x w j|) → L*(∑ j, |x v j-x w j|)≤r →
        ‖Z v-Z w‖^2≤L*(∑ j, |x v j-x w j|)*
          (9+8*Real.log (r/(L*(∑ j, |x v j-x w j|))))) ∧
      (∀ v w, c v=c w → L*(∑ j, |x v j-x w j|)=0 → Z v=Z w) := by
  obtain ⟨h,hh,ht⟩ := chart_l1_sq_hilbert c x (fun _ => L) (fun _ => hL)
  have hloc (v z y : ι) (hc : c v=c z) : |inner ℝ (P v-P z) (P y-P z)|≤‖h v-h z‖^2 := by
    rw [hh v z hc]; exact hl v z y hc
  obtain ⟨Q,Z,hQ,hZ,htri,hint,hcap,hsmall,hzero⟩ := triangle_repair c h ht hr P (capped_angle c h P hg hloc)
  refine ⟨Z,htri,?_,?_,?_⟩
  · intro v w
    rw [hZ]
    calc
      _ ≤ |‖P v-P w‖^2-q*‖θ v-θ w‖|+|‖Q v-Q w‖^2| := by
        convert abs_add_le (‖P v-P w‖^2-q*‖θ v-θ w‖) (‖Q v-Q w‖^2) using 1
        congr 1
        ring
      _ ≤ e+8*r := add_le_add (hm v w) (by simpa only [abs_sq] using hcap v w)
  · intro v w hc hpos hbound
    have hqr := hsmall v w hc (by rwa [hh v w hc]) (by rwa [hh v w hc])
    rw [hh v w hc] at hqr
    have hp := hl v w v hc
    rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hp
    rw [hZ]
    nlinarith
  · intro v w hc hz
    have hq := hzero v w hc (by rwa [hh v w hc])
    have hp := hl v w v hc
    rw [hz,real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hp
    have hzsq : ‖Z v-Z w‖^2=0 := by rw [hZ,hq,sub_self,norm_zero]; nlinarith [sq_nonneg ‖P v-P w‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq))

end
end UniformSparsestCut.ChartMetric

namespace UniformSparsestCut.GramMetric
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {V : Type u6} [Fintype V]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def localCost (N S : ℕ) (q k ε a b R γ : ℝ) : ℝ :=
  2*((k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*(k/ε*R))*Real.log (b/a)+
    (ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+(k/ε*R)^2+2*(k/ε*R)))/a)

def macroCost (N S : ℕ) (q k ε a b R T Rpos : ℝ) : ℝ :=
  q*(2*a+(2*T)^2/b)+4*ε*((S:ℝ)*N)*Real.log (b/a)+
    4*(ε*((S:ℝ)*N)*((k/ε*R)^2+2*(k/ε*R))*Real.log (b/a))+2*KernelApprox.cstar*q*Rpos

lemma localCost_nonneg {q k ε a b R γ : ℝ} (hq : 0≤q) (hk : 0≤k)
    (hε : 0<ε) (ha : 0<a) (hab : a≤b) (hR : 0≤R) (hγ : 0≤γ) :
    0≤localCost N S q k ε a b R γ := by
  have hl : 0≤Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  unfold localCost; positivity

lemma realization (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (c : V → Fin S) (x : V → F) (θ : V → E)
    {q k ε a b R T Rpos γ r : ℝ}
    (hq : 0<q) (hk : 0≤k) (hk1 : k≤1) (hε : 0<ε) (ha : 0<a) (hab : a≤b)
    (hR : 0≤R) (hT : 0≤T) (hγ : 0≤γ) (hkq : k=q^2/(N:ℝ))
    (hg : ∀ s i, ‖g s i‖≤2*q)
    (hB : ∀ s i, ‖B s (EuclideanSpace.single i 1)‖≤4*k)
    (hf : ∀ (s : Fin S) (w : E), ‖w‖≤2*T/a →
      ‖Real.exp (-‖w‖^2/2) • w-((N:ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) w) • g s i‖≤γ)
    (hx : ∀ v, ‖B (c v) (x v)‖≤T)
    (hrx : ∀ v, ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g (c v) i)) (B (c v)) (x v)‖≤R)
    (hpos : ∀ v, ‖B (c v) (x v)-θ v‖≤Rpos)
    (he : 0≤ macroCost N S q k ε a b R T Rpos) (hr : 0<r)
    (her : 3*macroCost N S q k ε a b R T Rpos/2≤r) :
    ∃ Z : V → EuclideanSpace ℝ V,
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*q*‖θ v-θ w‖|≤ macroCost N S q k ε a b R T Rpos+8*r) ∧
      (∀ v w, c v=c w → 0<localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|) →
        localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)≤r →
        ‖Z v-Z w‖^2≤localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)*
          (9+8*Real.log (r/(localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|))))) ∧
      (∀ v w, c v=c w → localCost N S q k ε a b R γ*(∑ i, |x v i-x w i|)=0 → Z v=Z w) := by
  let G : Fin S × Fin N → E := fun j => g j.1 j.2
  let Θ : V → E := fun v => B (c v) (x v)
  let α : V → Fin S × Fin N → ℝ := fun v => ChartKernel.alpha g B q k ε (c v) (x v)
  obtain ⟨P,hP⟩ := CommonKernel.gram_realization G Θ α hq.le hε.le ha hab
  have hPK (v w : V) : inner ℝ (P v) (P w)=Profile.kernel G q ε a b (Θ v) (Θ w) (α v) (α w) := by
    rw [hP,MetricKernel.gram_eq_kernel G Θ α q ε ha hab]
  have hPD (v w : V) : ‖P v-P w‖^2=ChartAngles.distance G q ε a b (Θ v) (Θ w) (α v) (α w) := by
    rw [norm_sub_sq_real]
    simp only [← real_inner_self_eq_norm_sq,hPK,ChartAngles.distance]
    ring
  have hα (v : V) (j : Fin S × Fin N) : |α v j|≤k/ε*R :=
    ChartKernel.alpha_norm_bound g B hk hε (c v) (x v) (hrx v) j
  have hd (v w : V) : |‖P v-P w‖^2-KernelApprox.cstar*q*‖θ v-θ w‖|≤ macroCost N S q k ε a b R T Rpos := by
    rw [hPD,norm_sub_rev (θ v) (θ w)]
    have hh := ChartAngles.rounded_distance_error (T := 2*T) G hq.le hε.le ha hab
      (mul_nonneg (div_nonneg hk hε.le) hR) (Θ v) (Θ w) (θ v) (θ w) (α v) (α w)
      (hα v) (hα w) (hpos v) (hpos w) ((norm_sub_le _ _).trans (by dsimp only [Θ]; linarith [hx v,hx w]))
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,macroCost] using hh
  have hlocal (v z y : V) (hc : c v=c z) :
      |inner ℝ (P v-P z) (P y-P z)|≤localCost N S q k ε a b R γ*(∑ i, |x v i-x z i|) := by
    have hb (w : V) := ChartAngles.local_profile g B hq hk hk1 hε ha hab hT hR hγ hkq hg hB hf
      (c z) (c w) (x z) (x v) (x w) (hx z) (by simpa only [← hc] using hx v) (hx w)
      (hrx z) (by simpa only [← hc] using hrx v) (hrx w)
    have hy := hb y
    have hz := hb z
    rw [inner_sub_left,inner_sub_right,inner_sub_right]
    simp only [hPK,Θ,α,G,hc] at hy hz ⊢
    have hy' := abs_le.mp hy
    have hz' := abs_le.mp hz
    rw [abs_le]
    unfold localCost
    constructor <;> linarith
  apply ChartMetric.repair_from_angles c (fun v i => x v i)
    (localCost_nonneg hq.le hk hε ha hab hR hγ) hr P θ hd ?_ hlocal
  intro v z y
  exact (neg_le_neg her).trans (ChartAngles.global_angle P θ
    (mul_nonneg KernelApprox.cstar_pos.le hq.le) he hd v z y)

end
end UniformSparsestCut.GramMetric

end

end OAI
