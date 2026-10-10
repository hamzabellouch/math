import OAI.Geometry.Convex.GeneralMahler.Brouwer.Grid

namespace OAI
/-! Brouwer fixed point for the standard simplex. -/
noncomputable section
open Set Filter Real Metric
open scoped Topology
namespace GeneralMahler
/-- Nonnegative weights of total mass one in the ambient function space. -/
abbrev simplexSet (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

lemma lattice_approx (f : (I→ℝ)→I→ℝ) (hf : MapsTo f (simplexSet I) (simplexSet I))
    (n:ℕ) :
    ∃ x ∈ simplexSet I, ∀ i:I, ∃ y ∈ simplexSet I,
      (∀ j:I, |x j-y j| ≤ Fintype.card I/((n+1:ℕ):ℝ)) ∧
        x i ≤ f y i + Fintype.card I/((n+1:ℕ):ℝ) := by
  let N := n+1
  have hp : (0:ℝ)<N := by dsimp [N]; positivity
  let F (x : Scarf.Grid I N) (i:I) : ℝ := (x.val i).val / (N:ℝ)
  have he (x) : F x ∈ simplexSet I := by
    refine ⟨fun i=>by dsimp only [F]; positivity,?_⟩
    dsimp only [F]
    rw [← Finset.sum_div,← Nat.cast_sum,x.property, div_self hp.ne']
  have hx (x) : ∃ i, F x i ≤ f (F x) i := by
    by_contra! hn
    have hu : ∑ i,f (F x) i < ∑ i, F x i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _=>hn i
    rw [(he x).2,(hf (he x)).2] at hu; exact lt_irrefl _ hu
  choose c hc using hx
  obtain ⟨b,s,⟨x,hx⟩,hl,hc'⟩ := Scarf.full_approx I N c
  let a : ℝ := Fintype.card I / (N:ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let B (i:I) : ℝ := b i / (N:ℝ)
  have hle (y : Scarf.Grid I N) (hy : Sum.inr y ∈ s) (i:I) :
      B i ≤ F y i ∧ F y i ≤ B i+a := by
    obtain ⟨h₁,h₂⟩ := hl y hy i
    dsimp only [B,F,a]
    rw [← add_div]
    constructor
    · gcongr
    · apply div_le_div_of_nonneg_right _ hp.le
      exact_mod_cast h₂
  refine ⟨F x,he x,fun i=>?_⟩
  obtain ⟨h₁,h₂⟩ := hle x hx i
  rcases hc' i with hi|⟨y,hy,hyi⟩
  · refine ⟨F x,he x,fun j=>by rw [sub_self,abs_zero]; exact ha,?_⟩
    have hu : B i=0 := by simp [B,hi]
    change _ ≤ _+a
    linarith [(hf (he x)).1 i]
  · refine ⟨F y,he y, fun j=>?_ ,?_⟩
    · change _ ≤ a; rw [abs_le]
      obtain ⟨h,h'⟩ := hle x hx j; obtain ⟨v,v'⟩ := hle y hy j
      constructor <;> linarith
    · change _ ≤ _+a
      have H := hc y; rw [hyi] at H
      exact h₂.trans (by linarith [(hle y hy i).1])

theorem BrouwerSimplex (f : (I→ℝ)→I→ℝ)
    (hf : MapsTo f (simplexSet I) (simplexSet I)) (hc : ContinuousOn f (simplexSet I)) :
    ∃ x ∈ simplexSet I, f x=x := by
  choose x hx y hy hd hle using lattice_approx f hf
  have hs : simplexSet I =
      Set.range (fun t : Convexity.StdSimplex ℝ I => (t.weights : I → ℝ)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext f
    simp only [simplexSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  have hk : IsCompact (simplexSet I) := by
    rw [hs]
    exact isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ I).continuous
  obtain ⟨z,hz,b,hm,hb⟩ := hk.tendsto_subseq hx
  have hu := tendsto_pi_nhds.mp hb
  have he : Tendsto (fun n => (Fintype.card I:ℝ)/((b n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    have hv := tendsto_natCast_atTop_atTop (R := ℝ) |>.comp hm.tendsto_atTop
    have ha : Tendsto (fun n => ((b n+1:ℕ):ℝ)) atTop atTop := by
      simp; exact tendsto_atTop_add_const_right _ _ hv
    simpa using ((tendsto_const_nhds (x := (Fintype.card I:ℝ))).div_atTop ha)
  have hv (i:I) : Tendsto (fun n=>y (b n) i) atTop (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have h₁ : Tendsto (fun n=>y (b n) i j - x (b n) j) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ he
      intro n
      rw [Real.norm_eq_abs,abs_sub_comm]
      exact hd _ _ _
    convert h₁.add (hu j) using 1 <;> simp
  have hh (i:I) : z i ≤ f z i := by
    have ha := hc z hz
    have h₁ : Tendsto (fun n=>y (b n) i) atTop (𝓝[simplexSet I] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hv i,Eventually.of_forall (fun n=>hy (b n) i)⟩
    have h₂ := tendsto_pi_nhds.mp (Tendsto.comp ha h₁) i
    have H := h₂.add he
    rw [add_zero] at H
    exact le_of_tendsto_of_tendsto (hu i) H (Eventually.of_forall fun n=>hle _ _)
  refine ⟨z,hz,funext fun i=>?_⟩
  by_contra hn
  have h : ∑ i,z i < ∑ i,f z i :=
    Finset.sum_lt_sum (fun j _=>hh j) ⟨i,Finset.mem_univ _,lt_of_le_of_ne (hh i) (Ne.symm hn)⟩
  rw [hz.2,(hf hz).2] at h
  exact lt_irrefl _ h
end GeneralMahler

end

end OAI
