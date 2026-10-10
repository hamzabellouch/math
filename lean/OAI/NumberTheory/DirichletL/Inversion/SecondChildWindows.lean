import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass
import OAI.NumberTheory.DirichletL.Descent.FreshWindows

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseSecondChildWindows
open InverseMoment InverseSecondProfileUniform
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O

theorem positive_cutoff (a b : ℝ) (ha : 0<a) (_hab : a≤b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      (∀ x∈Set.Icc a b,w x=1) ∧ tsupport (w : ℝ→ℂ)⊆Set.Icc (a/2) (b+1) := by
  have hKU : Set.Icc a b⊆Set.Ioo (a/2) (b+1) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hKU
  let v : ℝ→ℂ := fun x => (f x:ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp (by simpa using hf)
  have hvs : Function.support v⊆Set.Icc (a/2) (b+1) := by
    intro x hx
    have hh : x∈Function.support f := by simpa [v,Function.mem_support] using hx
    rw [hs] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  change (f x:ℂ)=1
  rw [(hone x).mp hx]
  rfl

theorem positiveSource_log_bound (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (_hm : 0≤m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤c) (hcb : c≤bcap) (_hx : 0<x)
    (hn : positiveSource g c θ x≠0) : |Real.log x|≤m+Real.log bcap := by
  have hc0 : 0<c := zero_lt_one.trans_le hc
  have hgn : g (Real.log x+Real.log c)≠0 := (mul_ne_zero_iff.mp hn).2
  have hh := hs hgn
  have hcl : 0≤Real.log c := Real.log_nonneg hc
  have hclb : Real.log c≤Real.log bcap := Real.log_le_log hc0 hcb
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem positiveSource_ratio_support (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (hm : 0≤m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤c) (hcb : c≤bcap) (hx : 0<x)
    (hn : positiveSource g c θ x≠0) :
    x∈Set.Icc (Real.exp (-(m+Real.log bcap))) (Real.exp (m+Real.log bcap)) := by
  have hh := (abs_le.mp (positiveSource_log_bound g m bcap c θ x hm hs hc hcb hx hn))
  exact ⟨(Real.le_log_iff_exp_le hx).mp hh.1,(Real.log_le_iff_le_exp hx).mp hh.2⟩

theorem translated_log_bound (a b x ρ B : ℝ) (ha : 0<a)
    (hx : x∈Set.Icc a b) (hρ : |ρ|≤B) :
    |Real.log x+ρ|≤|Real.log a|+|Real.log b|+B := by
  have hx0 := ha.trans_le hx.1
  have hlo := Real.log_le_log ha hx.1
  have hhi := Real.log_le_log hx0 hx.2
  have hl : |Real.log x|≤|Real.log a|+|Real.log b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  exact (abs_add_le _ _).trans (add_le_add hl hρ)

def outerIndex (i : Fin 4) : Fin 6 := i.castLE (by decide)

theorem fixed_windows (m bcap : ℝ) (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm : 0≤m) (_hcap : 1≤bcap) (hlo : ∀ i,0<lo i)
    (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w : 𝓢(ℝ,ℂ)) (U : Fin 6→𝓢(ℝ,ℂ)) (M : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M i) ∧ (∀ i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀ (g : 𝓢(ℝ,ℂ)),Function.support g⊆Set.Icc (-m) m →
        ∀ (c θ u v n : ℝ),1≤c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → 0<n →
        positiveSource g c θ (u*v*n)≠0 → w n=1) ∧
      (∀ (q : Fin 6→ℝ) (ρ : Fin 6→ℝ),
        (∀ i,|ρ i|≤Bρ i) →
        (∀ i : Fin 4,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w (q 4)≠0 → w (q 5)≠0 → ∀ i,U i (Real.log (q i)+ρ i)=1) := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 2)
  let b := Real.exp R/(lo 0*lo 2)
  have hhi0 (i : Fin 4) : 0<hi i := (hlo i).trans_le (hhi i)
  have ha : 0<a := div_pos (Real.exp_pos _) (mul_pos (hhi0 0) (hhi0 2))
  have hb : 0<b := div_pos (Real.exp_pos _) (mul_pos (hlo 0) (hlo 2))
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  let l : Fin 6→ℝ := ![lo 0,lo 1,lo 2,lo 3,a/2,a/2]
  let u : Fin 6→ℝ := ![hi 0,hi 1,hi 2,hi 3,(a+b+1)+1,(a+b+1)+1]
  have hl (i : Fin 6) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact half_pos ha
    · exact half_pos ha
  let H (i : Fin 6) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 6) : 0≤H i := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 6 => FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 6) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w,U,(fun i=>H i+1),a/2,(a+b+1)+1,half_pos ha,by linarith,hwc,hws,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),?_,?_⟩
  · intro g hg c θ u v n hc hcb hu hv hn hnz
    have hu0 := (hlo 0).trans_le hu.1
    have hv0 := (hlo 2).trans_le hv.1
    have hs := positiveSource_ratio_support g m bcap c θ (u*v*n) hm hg hc hcb
      (mul_pos (mul_pos hu0 hv0) hn) hnz
    have hnlo : a≤n := by
      apply (div_le_iff₀ (mul_pos (hhi0 0) (hhi0 2))).mpr
      calc
        _ ≤ u*v*n := hs.1
        _ ≤ (hi 0*hi 2)*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.2 hv.2 hv0.le (hhi0 0).le) hn.le
        _ = _ := by ring
    have hnhi : n≤b := by
      apply (le_div_iff₀ (mul_pos (hlo 0) (hlo 2))).mpr
      calc
        _ = (lo 0*lo 2)*n := by ring
        _ ≤ u*v*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.1 hv.1 (hlo 2).le hu0.le) hn.le
        _ ≤ _ := hs.2
    exact hwone n ⟨hnlo,by linarith⟩
  · intro q ρ hρ hblock hleft hright i
    have hq (k : Fin 6) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hws (subset_tsupport _ hleft)
      · exact hws (subset_tsupport _ hright)
    exact hVone i _ (translated_log_bound (l i) (u i) (q i) (ρ i) (Bρ i) (hl i) (hq i) (hρ i))

def actualOuterRatios {ι : Type*} [DecidableEq ι] (p : ι→O)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (G E V B : ℝ) : Fin 4→ℝ :=
  ![primeProductNorm p x.second.sourceCommon/G,
    ‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.second.divisor)‖^2/E,
    primeProductNorm p x.second.overlap/V,‖ConcreteTraceCRT.eisEmbedding x.second.frequency‖^2/B]

lemma actualRelativeNorm_outer {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (Q₁ Q₂ : Finset ι) (G E V B X : ℝ) (i : Fin 4) :
    secondRelativeNorm (secondActualNorms p (secondInheritedProfile p x Ψ m z) Q₁ Q₂)
      G E V B X (outerIndex i)=actualOuterRatios p x G E V B i := by
  fin_cases i <;> rfl

theorem actual_second_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm₁ : 0≤m₁) (_hm₂ : 0≤m₂) (hcap : 1≤bcap)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w₁ w₂ : 𝓢(ℝ,ℂ)) (U₀ : Fin 6→𝓢(ℝ,ℂ)) (M₀ : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M₀ i) ∧ (∀ i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (_hp : ∀ i,p i≠0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (pool : Finset ι)
      (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex) (G E V B X : ℝ)
      (ρ : Fin 6→ℝ) (c₁ c₂ θ₁ θ₂ : ℝ),
      0<G → 0<E → 0<V → 0<B → 0<X →
      (∀ i,|ρ i|≤Bρ i) → 1≤c₁ → c₁≤bcap → 1≤c₂ → c₂≤bcap →
      (∀ x∈source,∀ i,actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        star (positiveSource g₁ c₁ θ₁
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X)))≠0 →
        w₁ (primeProductNorm p Q/X)=1) ∧
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        positiveSource g₂ c₂ θ₂
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X))≠0 →
        w₂ (primeProductNorm p Q/X)=1) ∧
      (∀ j∈secondProfileIndices source pool (fun x=>secondInheritedProfile p x Ψ m z),
        w₁ (primeProductNorm p j.2.1/X)≠0 → w₂ (primeProductNorm p j.2.2/X)≠0 → ∀ i,
        U₀ i (secondRelativeLog
          (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X i+ρ i)=1) := by
  let mmax := max m₁ m₂
  have hmmax : 0≤mmax := hm₁.trans (le_max_left _ _)
  have hg₁' : Function.support g₁⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₁ hx
    exact ⟨(neg_le_neg (le_max_left _ _)).trans h.1,h.2.trans (le_max_left _ _)⟩
  have hg₂' : Function.support g₂⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₂ hx
    exact ⟨(neg_le_neg (le_max_right _ _)).trans h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨w,U,M,a,b,ha,hab,hwc,hws,hM,hUc,hUs,hfresh,hcut⟩ :=
    fixed_windows mmax bcap lo hi Bρ hmmax hcap hlo hhi hBρ
  refine ⟨w,w,U,M,a,b,ha,hab,hwc,hwc,hws,hws,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ Jo Jn source pool Ψ m z G E V B X ρ c₁ c₂ θ₁ θ₂ hG hE hV hB hX hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  have he (x : MarkedSecondSource ι Jo Jn) (Q : Finset ι) :
      (primeProductNorm p x.second.sourceCommon/G)*(primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X)=
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X) := by
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro x hx Q _ hn
    apply hfresh g₁ hg₁' c₁ θ₁ _ _ _ hc₁ hcb₁ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₁ c₁ θ₁ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact star_ne_zero.mp hn
  · intro x hx Q _ hn
    apply hfresh g₂ hg₂' c₂ θ₂ _ _ _ hc₂ hcb₂ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₂ c₂ θ₂ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact hn
  · intro j hj hleft hright i
    apply hcut (secondRelativeNorm
      (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X) ρ hρ
      (fun k=>?_) hleft hright i
    rw [actualRelativeNorm_outer]
    exact hblock j.1 ((mem_secondProfileIndices source pool _ j).mp hj).1 k

end SevenEighths.InverseSecondChildWindows

end

end OAI
