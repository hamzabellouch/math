import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays08
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays
open GlobalJoint
open RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal BoundedContinuousFunction NNReal
attribute [local instance] Classical.propDecidable
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
variable (coord : ∀ e,Fin (q (D.owner e)))

private lemma endpoint_joint_decay {a : ℕ} (X : ℕ→Fin a→ℕ) (Xp W M J : ℕ→ℕ)
    (hW : ∀ N,0<W N) (hX : ∀ N j,4*W N≤X N j) (hXp : ∀ N,4*W N≤Xp N)
    (hM : ∀ N,0<M N) (hJ : ∀ N,0<J N) (hWM : ∀ N,W N∣M N)
    (hr : Tendsto (fun N=>((M N*J N:ℕ):ℝ)/(Xp N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N))
      {z | ¬ fullCell (Xp N) (M N) (J N) z.2}) atTop (𝓝 0) := by
  have hb : ∀ N,(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real
      {z | ¬ fullCell (Xp N) (M N) (J N) z.2} ≤ 24*(((M N*J N:ℕ):ℝ)/(Xp N:ℝ)) := by
    intro N
    have heq : (jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real
        {z | ¬ fullCell (Xp N) (M N) (J N) z.2} =
      (RawHarmonicProbability.law (Xp N) (W N) (hW N) (hXp N) : Measure ℕ).real
        (RawSmallCells.partialCells (Xp N) (W N) (M N*J N) : Set ℕ) := by
      rw [←pivot_marginal (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)]
      apply measureReal_congr
      filter_upwards [joint_ae_fullDomain (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)] with z hz
      obtain ⟨hz,hcop⟩:=Finset.mem_filter.mp hz
      have hp : z.2∈RawHarmonicProbability.units (Xp N) (W N):=
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).2,hcop⟩
      change (¬fullCell (Xp N) (M N) (J N) z.2) =
        (z.2∈RawSmallCells.partialCells (Xp N) (W N) (M N*J N))
      simp only [fullCell,RawSmallCells.partialCells,Finset.mem_filter,hp,true_and]
      congr 3 <;> ring
    rw [heq]
    have hm : W N≤M N*J N := (Nat.le_of_dvd (hM N) (hWM N)).trans
      (Nat.le_mul_of_pos_right _ (hJ N))
    simpa only [mul_div_assoc] using RawSmallCells.partial_cost_simple
      (Xp N) (W N) (M N*J N) (hW N) (hXp N) hm
  have ht : Tendsto (fun N=>(jointLaw (X N) (Xp N) (W N) (hW N) (hX N) (hXp N)).real
      {z | ¬ fullCell (Xp N) (M N) (J N) z.2}) atTop (𝓝 0) :=
    squeeze_zero (fun _=>measureReal_nonneg) hb (by simpa using hr.const_mul 24)
  apply (ENNReal.tendsto_toReal_iff (by intro N;finiteness) (by simp)).mp
  simpa only [measureReal_def,ENNReal.toReal_zero] using ht

 

theorem source_harmonic_final
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (hmono : ∀ t i,Monotone (w t i)) (s : ℕ)
    (h0 : ∀ t i,(A t i).level 0=⊤) (h1 : ∀ t i,(A t i).level 1=⊤)
    (hs : ∀ t i,(A t i).level (s+1)=⊥)
    (a : ℕ) (m h : Fin D.targets→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ t (u : ℝ),0<u →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)^u) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : ∀ t,Tendsto (fun N=>(Q N+(∏ l : Fin (m t),(X N (perm t (l.castAdd (h t))):ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N) (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m t)),Tendsto (fun N=>(X N (perm t (j.castAdd (h t))):ℝ)/(L N:ℝ)) atTop atTop)
    (g x : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→∀ i,G t i)
    (slot : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ)
    (qval : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ)
    (hQ : ∀ t N y,y∈outsideDomain (fun l : Fin (h t)=>X N (perm t (l.natAdd (m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (m t)=>X N (perm t (l.castAdd (h t)))) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval t N y b k:ℝ)|≤Q N)
    (metric : ∀ t i,MetricSpace ((G t i)⧸Γ t i))
    (hmetric : ∀ t i,QuotientGroup.instTopologicalSpace (Γ t i)=(metric t i).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
    ∀ (Obs : ℕ→((Fin a→ℕ)×ℕ)→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Kobs : ℝ≥0) (Bobs : ℝ)
    (_hLip : ∀ N z t i,LipschitzWith Kobs (Obs N z t i))
    (_hBound : ∀ N z t i y,|Obs N z t i y|≤Bobs)
    (J : ℕ→ℕ) (_hJ : ∀ N,0<J N) (_hRJ : ∀ N,R N=(M N:ℝ)*(J N:ℝ))
    (r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs Bs : Finset (Scale a₀)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs1 D Fs Bs∣q₀)
    (b : Scale a₀) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ),
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) {z | cellRatio (Xp N) (primorial (w0 N)) (M N) (J N) z.2 (primorial_pos _) (hXp N)
          {k | QuotientGroup.mk (rawLocalOrbit D G n q c hsk A w hA hw m h perm
            (M N) (J N) (L N) (R N) (fun t=>g t N) (fun t=>x t N)
            (fun t=>slot t N) (fun t=>qval t N) z (k:ℤ)) ∈
            intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
          ≤ ((pivotOptions s r hs1 D Fs).card : ℝ)⁻¹/3}) atTop (𝓝 0)
 := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  have hd:=source_harmonic_decay D G n q c hsk A w hA hw Γ coord
    hΓ hmono s h0 h1 hs a m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0
    hSize hWM hM hMs hL hsm hWL hML hLexact hXL g x slot qval hQ metric hmetric
    Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  have hr : Tendsto (fun N=>((M N*J N:ℕ):ℝ)/(Xp N:ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul,←hRJ] using hRX
  have he:=endpoint_joint_decay X Xp (fun N=>primorial (w0 N)) M J
    (fun N=>primorial_pos _) hX hXp hM hJ (fun N=>by exact_mod_cast hWM N) hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using he.add hd) (fun N=>bot_le) ?_
  intro N
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  intro z hz
  by_cases hf : fullCell (Xp N) (M N) (J N) z.2
  · exact Or.inr ⟨hf,hz⟩
  · exact Or.inl hf

end SourceIntegerArrays
end

noncomputable section
namespace SourceMacroSelection
open ProductExposureLabels
open scoped BigOperators
 
def width {m : ℕ} (R : ℕ) (b : Label m) : ℤ := (∏ j,(2:ℤ)^(b.dyadic j))*(R:ℤ)
def left {m : ℕ} (R : ℕ) (b : Label m) : ℤ := b.bin*width R b
 

def Stable {m : ℕ} (C H R : ℕ) (b : Label m) : Prop :=
  (left R b-(C:ℤ)*width R b)/(H:ℤ)=
    (left R b+((C:ℤ)+1)*width R b)/(H:ℤ)
def modelBin {m : ℕ} (H R : ℕ) (b : Label m) : ℤ := left R b/(H:ℤ)
end SourceMacroSelection
end

noncomputable section
namespace SourceMacroSelection
open ProductExposureLabels
open scoped BigOperators

lemma width_cast {m : ℕ} (R : ℕ) (b : Label m) : (width R b:ℝ)=b.width (R:ℝ) := by
  simp [width,ProductExposureLabels.Label.width,ProductExposureLabels.Label.scales]
lemma left_cast {m : ℕ} (R : ℕ) (b : Label m) : (left R b:ℝ)=b.left (R:ℝ) := by
  simp [left,ProductExposureLabels.Label.left,width_cast]
lemma width_nonneg {m : ℕ} (R : ℕ) (b : Label m) : 0≤width R b := by
  unfold width
  positivity

lemma stable_value {m : ℕ} (C H R : ℕ) (hH : 0<H) (b : Label m) (hs : Stable C H R b)
    (z : ℤ) (hz : left R b-(C:ℤ)*width R b≤z ∧
      z≤left R b+((C:ℤ)+1)*width R b) : z/(H:ℤ)=modelBin H R b := by
  have hh : (0:ℤ)<H := by exact_mod_cast hH
  have hl:=Int.ediv_le_ediv hh hz.1
  have hu:=Int.ediv_le_ediv hh hz.2
  have hc : (0:ℤ)≤C := by positivity
  have hmlo : left R b-(C:ℤ)*width R b≤left R b := by nlinarith [width_nonneg R b]
  have hmhi : left R b≤left R b+((C:ℤ)+1)*width R b := by nlinarith [width_nonneg R b]
  have hlo:=Int.ediv_le_ediv hh hmlo
  have hhi:=Int.ediv_le_ediv hh hmhi
  change _=_ at hs
  unfold modelBin
  omega

 

lemma unstable_subset_boundary {m : ℕ} (C H R : ℕ) (hH : 0<H) (hR : 0<R)
    (L M : ℤ) (z : (Fin m→ℕ)×ℕ) (ht : ∀ j,0<z.1 j)
    (hp : (C+1)*R≤z.2)
    (hb : ¬Stable C H R (expose L M (R:ℝ) z)) :
    (∏ j,z.1 j)*(z.2-(C+1)*R)/H≠(∏ j,z.1 j)*(z.2+(C+1)*R)/H := by
  let b:=expose L M (R:ℝ) z
  let t : ℕ:=∏ j,z.1 j
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have hh : (0:ℤ)<H := by exact_mod_cast hH
  obtain ⟨hdy,hlo,hhi⟩:=expose_bounds L M (R:ℝ) hr z ht
  obtain ⟨htlo,htup⟩:=product_dyadic_bounds b z.1 hdy
  have htcast : (∏ j,(z.1 j:ℝ))=(t:ℝ) := by dsimp [t];simp
  rw [htcast] at hlo hhi htlo htup
  have hw : (width R b:ℝ)≤(t:ℝ)*(R:ℝ) := by
    rw [width_cast]
    exact mul_le_mul_of_nonneg_right htlo hr.le
  have hlowreal : ((t*(z.2-(C+1)*R):ℕ):ℝ)≤(left R b-(C:ℤ)*width R b:ℤ) := by
    rw [Nat.cast_mul,Nat.cast_sub hp]
    push_cast
    rw [left_cast,width_cast] at *
    have hc : (0:ℝ)≤C := by positivity
    have hmm := mul_nonneg (show (0:ℝ)≤(C:ℝ)+1 by positivity) (sub_nonneg.mpr hw)
    nlinarith
  have huppreal : ((left R b+((C:ℤ)+1)*width R b:ℤ):ℝ)≤((t*(z.2+(C+1)*R):ℕ):ℝ) := by
    push_cast
    rw [left_cast,width_cast] at *
    have hmm := mul_le_mul_of_nonneg_left hw (show (0:ℝ)≤(C:ℝ)+1 by positivity)
    nlinarith
  have hl : ((t*(z.2-(C+1)*R):ℕ):ℤ)≤left R b-(C:ℤ)*width R b := by exact_mod_cast hlowreal
  have hu : left R b+((C:ℤ)+1)*width R b≤((t*(z.2+(C+1)*R):ℕ):ℤ) := by exact_mod_cast huppreal
  have hlo' := Int.ediv_le_ediv hh hl
  have hhi' := Int.ediv_le_ediv hh hu
  have hmid : (left R b-(C:ℤ)*width R b)/(H:ℤ)≤
      (left R b+((C:ℤ)+1)*width R b)/(H:ℤ) := by
    apply Int.ediv_le_ediv hh
    have hc : (0:ℤ)≤C := by positivity
    nlinarith [width_nonneg R b]
  intro he
  have he' : ((t*(z.2-(C+1)*R):ℕ):ℤ)/(H:ℤ)=((t*(z.2+(C+1)*R):ℕ):ℤ)/(H:ℤ) := by
    exact_mod_cast he
  apply hb
  change (left R b-(C:ℤ)*width R b)/(H:ℤ)=
    (left R b+((C:ℤ)+1)*width R b)/(H:ℤ)
  omega

end SourceMacroSelection
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators
 
def number {m v q : ℕ} (M : ℕ) (L : ℤ) (b : Label m)
    (tail : Fin m→ℤ) (pstar slot : ℤ) (pattern : Fin (v+1)→ℤ)
    (β : Fin (v+1)→ℤ) (qval u : Fin q→ℤ) : ℤ :=
  (∏ j,tail j)*(pstar+(M:ℤ)*(∑ j,pattern j*β j)+slot)+
    (M:ℤ)*(∑ e,shift M L (qval e) b tail*u e)
 

def pieceModel {G : Type} [Group G] (Γ : Subgroup G) (M H : ℕ)
    (g x : ℤ→ℤ→G) (obs : ℤ→ℤ→(G⧸Γ)→ℝ) (N : ℤ) : ℝ :=
  obs (N/(H:ℤ)) (N%(M:ℤ))
    (QuotientGroup.mk ((g (N/(H:ℤ)) (N%(M:ℤ)))^((N-N%(M:ℤ))/(M:ℤ))*
      x (N/(H:ℤ)) (N%(M:ℤ))))
end SourceIntegerArrays
end

end

end OAI
