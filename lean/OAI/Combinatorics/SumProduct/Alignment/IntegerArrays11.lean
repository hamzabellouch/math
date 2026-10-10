import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays10
import OAI.Combinatorics.SumProduct.Alignment.MacroSelection02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter Topology
open scoped BigOperators
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open SourceResidueAlignment ProductExposureLabels SourceMacroSelection
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open Filter RoughFaceShift RoughScales IntegerAlignment
open RoughSamplingWeights RoughSourceExceptional RoughProductRemoval ProductExposureLaw
open RawHarmonicProbability
open MicrocellScale AdmissibleMicrocellBoundary
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))

 

structure ModelFamily (a : ℕ) where
  m : Fin D.targets→ℕ
  h : Fin D.targets→ℕ
  perm : ∀ t,Fin (m t+h t)≃Fin a
  M : ℕ→ℕ
  J : ℕ→ℕ
  R : ℕ→ℕ
  L : ℕ→ℤ
  H : ℕ→ℕ
  slot : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ
  qval : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ
  g : ∀ t,ℕ→(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→G t i
  x : ∀ t,ℕ→(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→G t i
  obs : ∀ t,ℕ→(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→((G t i)⧸Γ t i) →ᵇ ℝ
namespace ModelFamily
variable {D G q Γ} {a : ℕ} (d : ModelFamily D G q Γ a)
def atTime (N : ℕ) : RawModels D G q Γ a :=
  ⟨d.m,d.h,d.perm,d.M N,d.J N,d.R N,d.L N,fun _=>d.H N,
    fun t=>d.slot t N,fun t=>d.qval t N,fun t=>d.g t N,fun t=>d.x t N,fun t=>d.obs t N⟩
end ModelFamily
include hsk hA hw

 

theorem source_model_harmonic
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (hmono : ∀ t i,Monotone (w t i)) (s : ℕ)
    (h0 : ∀ t i,(A t i).level 0=⊤) (h1 : ∀ t i,(A t i).level 1=⊤)
    (hs : ∀ t i,(A t i).level (s+1)=⊥)
    (a : ℕ) (d : ModelFamily D G q Γ a)
    (w0 Xp P : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (Q : ℕ→ℝ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(d.M N:ℤ))
    (hM : ∀ N,0<d.M N) (hMs : ∀ N,RoughScales.Smooth (w0 N) (d.M N:ℤ))
    (hJ : ∀ N,0<d.J N) (hRJ : ∀ N,d.R N=d.M N*d.J N)
    (hL : ∀ N,0<d.L N) (hsm : ∀ N,RoughScales.Smooth (w0 N) (d.L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣d.L N) (hML : ∀ N,(d.M N:ℤ)∣d.L N)
    (hLexact : ∀ N,d.L N=(d.M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (d.m t)),Tendsto (fun N=>(X N (d.perm t (j.castAdd (d.h t))):ℝ)/(d.L N:ℝ)) atTop atTop)
    (hH : ∀ N,0<d.H N) (hP : ∀ N,0<P N)
    (hRrad : ∀ N,d.R N=radius (d.M N) (d.H N))
    (hd : Dominates (fun N=>(d.H N:ℝ)) (earlierScale d.M P))
    (hx : Dominates (fun N=>Real.log (Xp N:ℝ)) (fun N=>(d.H N:ℝ)))
    (hprod : ∀ t,∀ᶠ N in atTop,(∀ j : Fin (d.m t),X N (d.perm t (j.castAdd (d.h t)))≤P N) ∧
      (∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)≤(P N:ℝ)^2)
    (hQ0 : ∀ N,0≤Q N) (hQsize : ∀ᶠ N in atTop,Q N≤(d.M N:ℝ)*(P N:ℝ)^2)
    (hLsize : ∀ᶠ N in atTop,(d.L N:ℝ)≤(d.M N:ℝ)^2)
    (K : ℝ) (hK : 0≤K)
    (hslot : ∀ t N y,y∈outsideDomain (fun l : Fin (d.h t)=>X N (d.perm t (l.natAdd (d.m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (d.m t)=>X N (d.perm t (l.castAdd (d.h t)))) (Xp N) (primorial (w0 N))).image
      (expose (d.L N) (d.M N:ℤ) (d.R N:ℝ)) →∀ i,|(d.slot t N y b i:ℝ)|≤K*(d.L N:ℝ))
    (hQ : ∀ t N y,y∈outsideDomain (fun l : Fin (d.h t)=>X N (d.perm t (l.natAdd (d.m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (d.m t)=>X N (d.perm t (l.castAdd (d.h t)))) (Xp N) (primorial (w0 N))).image
      (expose (d.L N) (d.M N:ℤ) (d.R N:ℝ)) →∀ k,|(d.qval t N y b k:ℝ)|≤Q N)
    (metric : ∀ t i,MetricSpace ((G t i)⧸Γ t i))
    (hmetric : ∀ t i,QuotientGroup.instTopologicalSpace (Γ t i)=(metric t i).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
    ∀ (Kobs : ℝ≥0) (Bobs : ℝ)
    (_hLip : ∀ t N y i b r,LipschitzWith Kobs (d.obs t N y i b r))
    (_hBound : ∀ t N y i b r z,|d.obs t N y i b r z|≤Bobs)
    (r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs Bs : Finset (Scale a₀)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs1 D Fs Bs∣q₀)
    (b : Scale a₀) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ)
    (_hinput : ∀ p∈pivotOptions s r hs1 D Fs,∀ i : Comparison D Fs r,
      ∑ e,|(ownInput D q coord i.2.1.1
        (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd e:ℝ)|≤K),
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N))
      {z | cellRatio (Xp N) (primorial (w0 N)) (d.M N) (d.J N) z.2 (primorial_pos _) (hXp N)
        {k | ((d.atTime N).localModel z).modelSuccess coord (k:ℤ) s r hs1 formula Fs q₀ b τ}
        ≤((pivotOptions s r hs1 D Fs).card:ℝ)⁻¹/3}) atTop (𝓝 0)
 := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Kobs Bobs hLip hBound r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ hinput
  have hR (N : ℕ) : 0<d.R N:=by rw [hRJ];exact Nat.mul_pos (hM N) (hJ N)
  have hRreal (N : ℕ) : (0:ℝ)<d.R N:=by exact_mod_cast hR N
  have hrates (t : Fin D.targets) := AdmissibleArrayScales.source_array_scales
    d.M P d.H Xp (fun N j=>X N (d.perm t (j.castAdd (d.h t)))) Q (fun N=>(d.L N:ℝ))
    (Filter.Eventually.of_forall (fun N=>⟨hM N,hP N,hH N⟩)) hd hx (hprod t)
    (hQsize.mono (fun N hn=>⟨hQ0 N,hn⟩))
    (hLsize.mono (fun N hn=>⟨by exact_mod_cast (hL N).le,hn⟩))
  have hRX : Tendsto (fun N=>(d.R N:ℝ)/(Xp N:ℝ)) atTop (𝓝 0) := by
    have hh:=(enlarged_rates 1 (Filter.Eventually.of_forall hM)
      (Filter.Eventually.of_forall hH) hd hx).2
    simpa only [Nat.one_mul,←hRrad] using hh
  have hZ : ∀ t (u : ℝ),0<u →Tendsto (fun N=>((d.R N:ℝ)/(d.M N:ℝ))/
      (1+∑ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)^u) atTop atTop := by
    intro t u hu
    simpa only [←hRrad] using (hrates t).2.2.1 u hu
  have hSize : ∀ t,Tendsto (fun N=>(Q N+(∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)*(d.L N:ℝ))/(d.R N:ℝ))
      atTop (𝓝 0) := by
    intro t
    simpa only [←hRrad] using (hrates t).2.2.2
  let Obs := fun N z=>( (d.atTime N).localModel z).frozenObs
  let I : ℕ→Set ((Fin a→ℕ)×ℕ) := fun N=>
    {z | cellRatio (Xp N) (primorial (w0 N)) (d.M N) (d.J N) z.2 (primorial_pos _) (hXp N)
      {k | QuotientGroup.mk ((d.atTime N).orbit n c hsk A w hA hw z (k:ℤ))∈
        intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
      ≤((pivotOptions s r hs1 D Fs).card:ℝ)⁻¹/3}
  let S : ℕ→Set ((Fin a→ℕ)×ℕ) := fun N=>
    {z | ∃ t,¬Stable (2^(d.m t)+1) (d.H N) (d.R N) ((d.atTime N).exposure z t)}
  let B : ℕ→Set ((Fin a→ℕ)×ℕ) := fun N=>
    {z | cellRatio (Xp N) (primorial (w0 N)) (d.M N) (d.J N) z.2 (primorial_pos _) (hXp N)
      {k | ((d.atTime N).localModel z).modelSuccess coord (k:ℤ) s r hs1 formula Fs q₀ b τ}
      ≤((pivotOptions s r hs1 D Fs).card:ℝ)⁻¹/3}
  have hi:=source_harmonic_final D G n q c hsk A w hA hw Γ coord hΓ hmono s h0 h1 hs
    a d.m d.h d.perm w0 d.M Xp X (fun N=>(d.R N:ℝ)) Q d.L hw0 hX hXp hXt hXpt
    hRreal hRX hZ hQ0 hSize hWM hM hMs hL hsm hWL hML hLexact hXL
    (fun t N=>(d.atTime N).selectedG t) (fun t N=>(d.atTime N).selectedX t) d.slot d.qval hQ
    metric hmetric Obs Kobs Bobs
    (fun N z t i=>hLip t N _ i _ _) (fun N z t i y=>hBound t N _ i _ _ y)
    d.J hJ (fun N=>by exact_mod_cast hRJ N) r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  change Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)) (I N))
    atTop (𝓝 0) at hi
  have hiReal : Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (I N))
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,measureReal_def,Function.comp_def] using (ENNReal.tendsto_toReal (show (0:ℝ≥0∞)≠⊤ by simp)).comp hi
  have hbase : ∀ᶠ N in atTop,0<d.M N ∧ primorial (w0 N)≤d.M N ∧ 0<d.H N := by
    apply Filter.Eventually.of_forall
    intro N
    refine ⟨hM N,?_,hH N⟩
    apply Nat.le_of_dvd (hM N)
    exact_mod_cast hWM N
  have hp' : ∀ t,∀ᶠ N in atTop,(∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))))^2)≤(P N)^2 := by
    intro t
    filter_upwards [hprod t] with N hn
    exact_mod_cast hn.2
  have hm:=source_joint_macro_decay d.m d.h d.perm (fun t=>2^(d.m t)+1)
    (fun N=>primorial (w0 N)) d.M P d.H Xp X d.L (fun N=>primorial_pos _) hX hXp hbase hd hx hp'
  have hsReal : Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (S N))
      atTop (𝓝 0) := by
    apply hm.congr
    intro N
    congr 1
    ext z
    simp only [S,Set.mem_ofPred_eq,RawModels.exposure,RawModels.inner,ModelFamily.atTime,←hRrad]
    rfl
  have hsmall : ∀ᶠ N in atTop,∀ t,2*K*(Q N+(∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)*(d.L N:ℝ))≤d.R N := by
    apply Filter.eventually_all.mpr
    intro t
    have hh : Tendsto (fun N=>2*K*((Q N+(∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)*(d.L N:ℝ))/(d.R N:ℝ)))
        atTop (𝓝 0) := by simpa using (hSize t).const_mul (2*K)
    filter_upwards [hh.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with N hn
    have hh' : (2*K*(Q N+(∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)*(d.L N:ℝ)))/(d.R N:ℝ)<1 := by
      simpa only [mul_div_assoc] using hn
    exact ((div_lt_iff₀ (hRreal N)).mp hh').le.trans_eq (one_mul _)
  have hbound : ∀ᶠ N in atTop,
      (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (B N)≤
      (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (S N)+
      (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (I N) := by
    filter_upwards [hsmall] with N hn
    rw [←joint_restrict_fullDomain (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N) (B N)]
    apply le_trans (measureReal_mono ?_) (measureReal_union_le (S N) (I N))
    rintro z ⟨hzB,hz⟩
    by_cases hstable : ∀ t,Stable (2^(d.m t)+1) (d.H N) (d.R N) ((d.atTime N).exposure z t)
    · apply Or.inr
      obtain ⟨hzraw,hzunit⟩:=Finset.mem_filter.mp hz
      obtain ⟨hzT,hzP⟩ : (∀ j,z.1 j∈units (X N j) (primorial (w0 N))) ∧
          z.2∈Finset.Ico (Xp N) ((Xp N)^2) := by
        simpa [rawDomain,Finset.product_eq_sprod] using hzraw
      have htail : ∀ t j,0<((d.atTime N).inner z t).1 j := by
        intro t j
        have hh:= (Finset.mem_Ico.mp (Finset.mem_filter.mp (hzT (d.perm t (j.castAdd (d.h t))))).1).1
        have hxj:=hX N (d.perm t (j.castAdd (d.h t)))
        have hw':=primorial_pos (w0 N)
        change 0<z.1 (d.perm t (j.castAdd (d.h t)))
        omega
      have hc : ∀ t,IsCoprime (∏ j,((d.atTime N).exposure z t).residue j) (d.L N) := by
        intro t
        apply IsCoprime.prod_left
        intro j _
        have htR : IntegerAlignment.Rough (w0 N) (z.1 (d.perm t (j.castAdd (d.h t))):ℤ) := by
          intro p hp hpw hpt
          have hpW : p∣primorial (w0 N):=hp.dvd_primorial_iff.mpr hpw
          have hpt' : p∣z.1 (d.perm t (j.castAdd (d.h t))):=by exact_mod_cast hpt
          have hcp:=(Finset.mem_filter.mp (hzT (d.perm t (j.castAdd (d.h t))))).2
          have hpd:=Nat.dvd_gcd hpW hpt'
          rw [hcp.gcd_eq_one] at hpd
          exact hp.ne_one (Nat.dvd_one.mp hpd)
        have hcp := (IntegerAlignment.coprime_smooth_rough (hsm N) htR).symm
        change IsCoprime ((z.1 (d.perm t (j.castAdd (d.h t))):ℤ)%(d.L N)) (d.L N)
        rw [Int.isCoprime_iff_gcd_eq_one,Int.gcd_emod]
        exact Int.isCoprime_iff_gcd_eq_one.mp hcp
      have hv : ∀ t,(∏ j,(((d.atTime N).inner z t).1 j:ℝ))≤
          ∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2 := by
        intro t
        apply Finset.prod_le_prod₀ (fun j _=>by positivity)
        intro j _
        exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp (hzT (d.perm t (j.castAdd (d.h t))))).1).2.le
      have ho (t : Fin D.targets) : (d.atTime N).outer z t∈
          outsideDomain (fun j : Fin (d.h t)=>X N (d.perm t (j.natAdd (d.m t)))) (primorial (w0 N)) := by
        apply Fintype.mem_piFinset.mpr
        intro j
        exact hzT _
      have hi' (t : Fin D.targets) : (d.atTime N).inner z t∈
          fullDomain (fun j : Fin (d.m t)=>X N (d.perm t (j.castAdd (d.h t)))) (Xp N) (primorial (w0 N)) := by
        apply Finset.mem_filter.mpr
        refine ⟨?_,hzunit⟩
        exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
          (fun j : Fin (d.m t)=>hzT (d.perm t (j.castAdd (d.h t)))),hzP⟩
      have hb' (t : Fin D.targets) : (d.atTime N).exposure z t∈
          (fullDomain (fun j : Fin (d.m t)=>X N (d.perm t (j.castAdd (d.h t)))) (Xp N) (primorial (w0 N))).image
            (expose (d.L N) (d.M N:ℤ) (d.R N:ℝ)) :=
        Finset.mem_image.mpr ⟨(d.atTime N).inner z t,hi' t,rfl⟩
      have he:=source_cell_model D G n q c hsk A w hA hw Γ coord (d.atTime N) z
        (hM N) (hJ N) (hRJ N) (hL N) (hML N) (fun _=>hH N) htail hstable hc
        K (Q N) (fun t=>∏ j : Fin (d.m t),(X N (d.perm t (j.castAdd (d.h t))):ℝ)^2)
        hK (hQ0 N) hv (fun t i=>hslot t N _ (ho t) _ (hb' t) i)
        (fun t e=>hQ t N _ (ho t) _ (hb' t) e) hn s r hs1 formula Fs q₀ b τ hinput
        (Xp N) (primorial (w0 N)) (primorial_pos _) (hXp N)
      dsimp only [I,B,Obs,Set.mem_ofPred_eq] at hzB ⊢
      exact he.le.trans hzB
    · exact Or.inl (not_forall.mp hstable)
  have hout : Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real (B N))
      atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun _=>measureReal_nonneg)) hbound
      (by simpa only [zero_add] using hsReal.add hiReal)
  exact (ENNReal.tendsto_toReal_zero_iff (fun _=>by finiteness)).mp hout

end SourceIntegerArrays.GlobalJoint

end
end

end OAI
