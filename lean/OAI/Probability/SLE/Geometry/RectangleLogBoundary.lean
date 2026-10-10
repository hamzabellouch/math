import OAI.Probability.SLE.Stochastic.LogRatioPaths

namespace OAI

/-! Explicit compatible logarithms on the four sides of a path-crossing
rectangle. No assertion about logarithms in its interior is made. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma exists_continuous_path_log (f : C(unitInterval,ℂ)) (hn : ∀ t, f t≠0)
    (a : ℂ) (ha : Complex.exp a=f 0) :
    ∃ L : C(unitInterval,ℂ), (∀ t, Complex.exp (L t)=f t) ∧ L 0=a := by
  let g : C(unitInterval,{z : ℂ // z≠0}) := ⟨fun t => ⟨f t,hn t⟩,f.continuous.subtype_mk _⟩
  obtain ⟨L,hL,h0⟩ := Complex.isCoveringMap_exp.exists_path_lifts g a (Subtype.ext ha.symm)
  exact ⟨L,fun t => congrArg Subtype.val (congr_fun hL t),h0⟩

lemma rectangle_difference_boundary_log (c p : C(unitInterval,ℂ))
    (hc : c 0=c 1) (hbase : ∀ s, c 0-p s≠0)
    (L₀ L₁ : C(unitInterval,ℂ))
    (hL₀ : ∀ t, Complex.exp (L₀ t)=c t-p 0)
    (hL₁ : ∀ t, Complex.exp (L₁ t)=c t-p 1)
    (h₀ : L₀ 0=L₀ 1) (h₁ : L₁ 0=L₁ 1) :
    ∃ K : C(unitInterval × unitInterval,ℂ), ∀ q,
      q.1=0 ∨ q.1=1 ∨ q.2=0 ∨ q.2=1 →
      Complex.exp (K q)=c q.2-p q.1 := by
  let f : C(unitInterval,ℂ) := ⟨fun s => c 0-p s,continuous_const.sub p.continuous⟩
  obtain ⟨B,hB,hB0⟩ := exists_continuous_path_log f hbase (L₀ 0) (hL₀ 0)
  let d := B 1-L₁ 0
  have hd : Complex.exp d=1 := by
    dsimp [d]
    rw [Complex.exp_sub,hB,hL₁]
    exact div_self (hbase 1)
  have hB1 : L₁ 0+d=B 1 := by dsimp [d]; ring
  let K : C(unitInterval × unitInterval,ℂ) :=
    ⟨fun q => (1-(q.1:ℂ))*L₀ q.2+(q.1:ℂ)*(L₁ q.2+d)+B q.1-
      (1-(q.1:ℂ))*B 0-(q.1:ℂ)*B 1,by fun_prop⟩
  refine ⟨K,fun q hq => ?_⟩
  rcases hq with hq | hq | hq | hq
  · have he : K q=L₀ q.2 := by simp [K,hq]
    rw [he,hL₀,hq]
  · have he : K q=L₁ q.2+d := by simp [K,hq]
    rw [he,Complex.exp_add,hd,mul_one,hL₁,hq]
  · have he : K q=B q.1 := by
      dsimp [K]
      rw [hq,hB0,hB1]
      ring
    rw [he,hB]
    simp [f,hq]
  · have he : K q=B q.1 := by
      dsimp [K]
      rw [hq,← h₀,← h₁,hB0,hB1]
      ring
    rw [he,hB]
    simp [f,hq,← hc]

end SLEExactGauge

end

end OAI
