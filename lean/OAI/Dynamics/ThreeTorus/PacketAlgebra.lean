import OAI.Dynamics.ThreeTorus.PacketStates
import OAI.Dynamics.ThreeTorus.PhysicalJets

namespace OAI

/-! Finite packet algebra and physical L2 metric estimates. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets

variable {ι κ : Type*}

def reindex (F : PassagePackets ι) (r : κ → ι) : PassagePackets κ where
  m := F.m ∘ r
  nonzero := fun i => F.nonzero (r i)
  A := F.A ∘ r
  A₀ := F.A₀ ∘ r
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := fun i => F.lift_matches (r i)
  two := fun i => F.two (r i)
  continuous_lift := fun i => F.continuous_lift (r i)
  continuous_deriv := fun i => F.continuous_deriv (r i)
  smooth_lift := fun i => F.smooth_lift (r i)
  support_lift := fun i => F.support_lift (r i)
  continuous_amplitude := fun i => F.continuous_amplitude (r i)
  smooth_amplitude := fun i => F.smooth_amplitude (r i)
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

lemma reindex_good (F : PassagePackets ι) (r : κ → ι) {δ : ℝ} (h : F.GoodArc δ) :
    (F.reindex r).GoodArc δ := h

lemma reindex_reflection (F : PassagePackets ι) {r : κ → ι}
    {τ : ι → ι} {σ : κ → κ} (h : F.Reflection τ) (he : ∀ i, r (σ i)=τ (r i)) :
    (F.reindex r).Reflection σ := by
  constructor
  · intro i; change F.m (r (σ i)) = -F.m (r i); rw [he,h.index]
  · intro i p; change F.A (r (σ i)) p = conj (F.A (r i) p); rw [he,h.amplitude]
  · intro i a x; change F.A₀ (r (σ i)) a x = conj (F.A₀ (r i) a x); rw [he,h.lift]

/-- Two arbitrary smooth packet lists in the SAME good arc and speed may be
merged. The coefficient supports are not required to be disjoint. -/
def append (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (_hV : G.V=F.V) :
    PassagePackets (ι ⊕ κ) := by
  let l := min F.l G.l
  let u := max F.u G.u
  let R := min (l-δ) (1-δ-u)/4
  have hl : δ < l := lt_min hF.2.1 hG.2.1
  have hu : u < 1-δ := max_lt hF.2.2.1 hG.2.2.1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRl : 2*R < l-δ := by
    have ha : min (l-δ) (1-δ-u) ≤ l-δ := min_le_left _ _
    dsimp only [R]; linarith
  have hRu : 2*R < 1-δ-u := by
    have ha : min (l-δ) (1-δ-u) ≤ 1-δ-u := min_le_right _ _
    dsimp only [R]; linarith
  refine {
    m := Sum.elim F.m G.m
    nonzero := ?_
    A := Sum.elim F.A G.A
    A₀ := Sum.elim F.A₀ G.A₀
    o := 0
    l := l
    u := u
    R := R
    lo := hδ.trans hl.le
    uo := by linarith
    lu := (min_le_left _ _).trans (F.lu.trans (le_max_left _ _))
    Rpos := hR
    lift_matches := ?_
    two := ?_
    continuous_lift := ?_
    continuous_deriv := ?_
    smooth_lift := ?_
    support_lift := ?_
    continuous_amplitude := ?_
    smooth_amplitude := ?_
    V := F.V
    periodic := F.periodic
    smooth_speed := F.smooth_speed
    positive_deriv := ?_ }
  · intro i; cases i with
    | inl i => exact F.nonzero i
    | inr i => exact G.nonzero i
  · intro i a x hx; cases i with
    | inl i => exact F.lift_matches i a x (by rwa [hF.1])
    | inr i => exact G.lift_matches i a x (by rwa [hG.1])
  · intro i; cases i with
    | inl i => exact F.two i
    | inr i => exact G.two i
  · intro i; cases i with
    | inl i => exact F.continuous_lift i
    | inr i => exact G.continuous_lift i
  · intro i; cases i with
    | inl i => exact F.continuous_deriv i
    | inr i => exact G.continuous_deriv i
  · intro i; cases i with
    | inl i => exact F.smooth_lift i
    | inr i => exact G.smooth_lift i
  · intro i a x hx; cases i with
    | inl i => exact ⟨(min_le_left _ _).trans_lt (F.support_lift i a hx).1,
        (F.support_lift i a hx).2.trans (le_max_left _ _)⟩
    | inr i => exact ⟨(min_le_right _ _).trans_lt (G.support_lift i a hx).1,
        (G.support_lift i a hx).2.trans (le_max_right _ _)⟩
  · intro i; cases i with
    | inl i => exact F.continuous_amplitude i
    | inr i => exact G.continuous_amplitude i
  · intro i; cases i with
    | inl i => exact F.smooth_amplitude i
    | inr i => exact G.smooth_amplitude i
  · intro x hx
    exact hF.2.2.2 x ⟨by linarith [hx.1],by linarith [hx.2]⟩

lemma append_good (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (hV : G.V=F.V) :
    (F.append G hδ hF hG hV).GoodArc δ :=
  ⟨rfl,lt_min hF.2.1 hG.2.1,max_lt hF.2.2.1 hG.2.2.1,hF.2.2.2⟩

lemma append_reflection (F : PassagePackets ι) (G : PassagePackets κ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : F.GoodArc δ) (hG : G.GoodArc δ) (hV : G.V=F.V)
    {τ : ι → ι} {σ : κ → κ} (hrF : F.Reflection τ) (hrG : G.Reflection σ) :
    (F.append G hδ hF hG hV).Reflection (Sum.map τ σ) := by
  constructor
  · intro i; cases i with
    | inl i => exact hrF.index i
    | inr i => exact hrG.index i
  · intro i p; cases i with
    | inl i => exact hrF.amplitude i p
    | inr i => exact hrG.amplitude i p
  · intro i a x; cases i with
    | inl i => exact hrF.lift i a x
    | inr i => exact hrG.lift i a x

/-- Finite regrouping of amplitudes. Used only for equal-mode terms; this
constructor does not assert an orthogonality or spectral identity. -/
def regroup [Fintype ι] (F : PassagePackets ι) (s : κ → Finset ι)
    (m : κ → ℤ) (hm : ∀ i, m i ≠ 0) (c : κ → ι → ℂ) : PassagePackets κ where
  m := m
  nonzero := hm
  A := fun i p => ∑ j ∈ s i, c i j * F.A j p
  A₀ := fun i a x => ∑ j ∈ s i, c i j * F.A₀ j a x
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := fun i a x hx => Finset.sum_congr rfl (fun j _ => by rw [F.lift_matches j a x hx])
  two := fun i a => ContDiff.sum (fun j _ => contDiff_const.mul (F.two j a))
  continuous_lift := fun i => continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_lift j))
  continuous_deriv := by
    intro i
    have hd (a : UnitAddCircle) (j : ι) : Differentiable ℝ (F.A₀ j a) :=
      (F.two j a).differentiable (by norm_num)
    have he : (fun p : UnitAddCircle × ℝ => deriv (fun x => ∑ j ∈ s i, c i j * F.A₀ j p.1 x) p.2) =
        fun p => ∑ j ∈ s i, c i j * deriv (F.A₀ j p.1) p.2 := by
      funext p
      rw [deriv_fun_sum (fun j _ => (hd p.1 j).differentiableAt.const_mul _)]
      exact Finset.sum_congr rfl (fun j _ => deriv_const_mul _ (hd p.1 j).differentiableAt)
    rw [he]
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_deriv j))
  smooth_lift := fun i => ContDiff.sum (fun j _ => contDiff_const.mul (F.smooth_lift j))
  support_lift := by
    intro i a x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    have hz : F.A₀ j a x = 0 := by by_contra hz; exact hn (F.support_lift j a hz)
    rw [hz,mul_zero]
  continuous_amplitude := fun i => continuous_finsetSum _ (fun j _ => continuous_const.mul (F.continuous_amplitude j))
  smooth_amplitude := fun i => ContDiff.sum (fun j _ => contDiff_const.mul (F.smooth_amplitude j))
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalDist (f g : TripleTorus → ℂ) : ℝ := Real.sqrt (physicalError f g)
lemma physicalDist_nonneg (f g : TripleTorus → ℂ) : 0 ≤ physicalDist f g := Real.sqrt_nonneg _
lemma physicalDist_sq (f g : TripleTorus → ℂ) : physicalDist f g^2=physicalError f g :=
  Real.sq_sqrt (physicalError_nonneg f g)
lemma physicalDist_lt_iff (f g : TripleTorus → ℂ) {ε : ℝ} (hε : 0 < ε) :
    physicalDist f g < ε ↔ physicalError f g < ε^2 := Real.sqrt_lt' hε
lemma physicalDist_symm (f g : TripleTorus → ℂ) : physicalDist f g=physicalDist g f := by
  simp only [physicalDist,physicalError,norm_sub_rev]
lemma physicalDist_chart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ passageChart H) (g ∘ passageChart H)=physicalDist f g := by
  rw [physicalDist,physicalError_chart hH]
  rfl
lemma physicalDist_equiv (e : TripleTorus ≃ᵐ TripleTorus)
    (he : MeasurePreserving e tripleVolume tripleVolume) (f g : TripleTorus → ℂ) :
    physicalDist (f ∘ e) (g ∘ e)=physicalDist f g := by
  exact congrArg Real.sqrt (he.integral_comp e.measurableEmbedding (fun x => ‖f x-g x‖^2))
lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 ν) : ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂ν := by
  calc
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂ν := L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
lemma physicalError_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalError f g=‖hf.toLp f-hg.toLp g‖^2 := by
  rw [← hf.toLp_sub hg,norm_toLp_sq]
  rfl
lemma physicalDist_eq_norm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g=‖hf.toLp f-hg.toLp g‖ := by
  rw [physicalDist,physicalError_eq_norm hf hg,Real.sqrt_sq (norm_nonneg _)]
lemma physicalDist_triangle {f g h : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) (hh : MemLp h 2 tripleVolume) :
    physicalDist f h ≤ physicalDist f g+physicalDist g h := by
  rw [physicalDist_eq_norm hf hh,physicalDist_eq_norm hf hg,physicalDist_eq_norm hg hh]
  simpa only [dist_eq_norm] using dist_triangle (hf.toLp f) (hg.toLp g) (hh.toLp h)
lemma physicalDist_finsum {ι : Type*} [Fintype ι] {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, MemLp (f i) 2 tripleVolume) (hg : ∀ i, MemLp (g i) 2 tripleVolume) :
    physicalDist (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤ ∑ i, physicalDist (f i) (g i) := by
  classical
  have hsum (a : ι → TripleTorus → ℂ) (ha : ∀ i, MemLp (a i) 2 tripleVolume) :
      (memLp_finsetSum Finset.univ (fun i _ => ha i)).toLp (fun x => ∑ i, a i x) =
        ∑ i, (ha i).toLp (a i) := by
    apply Lp.ext
    filter_upwards [(memLp_finsetSum Finset.univ (fun i _ => ha i)).coeFn_toLp,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i => (ha i).toLp (a i)),
      ae_all_iff.mpr (fun i => (ha i).coeFn_toLp)] with x hx hy hz
    rw [hx,hy]
    exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  rw [physicalDist_eq_norm (memLp_finsetSum Finset.univ (fun i _ => hf i))
    (memLp_finsetSum Finset.univ (fun i _ => hg i)),hsum f hf,hsum g hg,← Finset.sum_sub_distrib]
  simp_rw [physicalDist_eq_norm (hf _) (hg _)]
  exact norm_sum_le Finset.univ (fun i => (hf i).toLp (f i)-(hg i).toLp (g i))

end ThreeTorus
end
end

end OAI
