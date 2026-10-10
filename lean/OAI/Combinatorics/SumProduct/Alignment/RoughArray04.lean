import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
variable {τ : Type} [Fintype τ] {ι : τ→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : τ→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
 

theorem source_global_selected_faces
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    [∀ t,MetricSpace ((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
      lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))]
    (htop : ∀ t,(inferInstance : MetricSpace
      ((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)))
    (a : ℕ) (m h v : τ→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
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
    (pattern : ∀ t,ι t→Fin (v t+1)→ℤ)
    (g x : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→∀ i,G t i)
    (b0 b1 : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→ι t→ℝ)
    (qval : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ)
    (hQ : ∀ t N y,y∈outsideDomain (fun l : Fin (h t)=>X N (perm t (l.natAdd (m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (m t)=>X N (perm t (l.castAdd (h t)))) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval t N y b k:ℝ)|≤Q N)
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (hε : 0<ε)
    (hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ z : ℕ→(Fin a→ℕ)×ℕ,
      (∀ k,z k∈E (φ k) ∧ z k∈fullDomain (X (φ k)) (Xp (φ k)) (primorial (w0 (φ k)))) ∧
      ∀ t (e : Fin (q t)) (j : Fin (v t+1)) (d : ℕ),0<d → ∀ b : ℕ,∀ᶠ k in atTop,
        let y := fun l : Fin (h t)=>(z k).1 (perm t (l.natAdd (m t)))
        (fun l : Fin (m t)=>(z k).1 (perm t (l.castAdd (h t))),(z k).2) ∉
        rawPhysicalEvent (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))
          (m t) (v t) (1/((b:ℝ)+1)) ((b:ℝ)+1) (b+1) (1/((b:ℝ)+1))
          (R (φ k)) d (M (φ k)) (L (φ k))
          (fun l=>actualData (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (pattern t)
            (g t (φ k) y l) (x t (φ k) y l) (b0 t (φ k) y l) (b1 t (φ k) y l)
            (fun u=>(qval t (φ k) y l u:ℝ)/(M (φ k):ℝ))
            (fun u=>-(residueData (L (φ k)) (qval t (φ k) y l u) l:ℝ)/(M (φ k):ℝ)) e j
            (coarseOrigin (v t) (M (φ k)) (R (φ k)) l) (shift (M (φ k)) (L (φ k)) (qval t (φ k) y l e) l))
 := by
  classical
  let μ : ℕ→Measure ((Fin a→ℕ)×ℕ) := fun N=>
    jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)
  have (N : ℕ) : IsProbabilityMeasure (μ N) := by dsimp [μ]; infer_instance
  let E' (N : ℕ) := E N∩(fullDomain (X N) (Xp N) (primorial (w0 N)):Set _)
  have hE' (N : ℕ) : ε≤μ N (E' N) := by
    have heq : μ N (E' N)=μ N (E N) := by
      apply measure_congr
      filter_upwards [joint_ae_fullDomain (X N) (Xp N) (primorial (w0 N))
        (primorial_pos _) (hX N) (hXp N)] with z hz
      change (z∈E N ∧ z∈fullDomain (X N) (Xp N) (primorial (w0 N)))=(z∈E N)
      exact propext ⟨And.left,fun he=>⟨he,hz⟩⟩
    rw [heq]
    exact hE N
  let Face := Σ t : τ,Fin (q t)×Fin (v t+1)
  let OneBad : ℕ→Face→ℕ→Set ((Fin a→ℕ)×ℕ) := fun N face idx=>
    {z | let t := face.1
      let y := fun l : Fin (h t)=>z.1 (perm t (l.natAdd (m t)))
      (fun l : Fin (m t)=>z.1 (perm t (l.castAdd (h t))),z.2) ∈
        rawPhysicalEvent (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))
          (m t) (v t) (1/((idx.unpair.2:ℝ)+1)) ((idx.unpair.2:ℝ)+1) (idx.unpair.2+1)
          (1/((idx.unpair.2:ℝ)+1)) (R N) (idx.unpair.1+1) (M N) (L N)
          (fun l=>actualData (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (pattern t)
            (g t N y l) (x t N y l) (b0 t N y l) (b1 t N y l)
            (fun u=>(qval t N y l u:ℝ)/(M N:ℝ))
            (fun u=>-(residueData (L N) (qval t N y l u) l:ℝ)/(M N:ℝ)) face.2.1 face.2.2
            (coarseOrigin (v t) (M N) (R N) l) (shift (M N) (L N) (qval t N y l face.2.1) l))}
  have hOneBadReal (face : Face) (idx : ℕ) :
      Tendsto (fun N=>(μ N).real (OneBad N face idx)) atTop (𝓝 0) := by
    let t := face.1
    exact source_full_earlier_face_decay (G t) (n t) (q t) (c t) (hsk t) (A t)
      (w t) (hA t) (hw t) (Γ t) (hΓ t) (htop t)
      (m t) (h t) a (v t) (idx.unpair.1+1) (perm t) (by omega)
      (1/((idx.unpair.2:ℝ)+1)) ((idx.unpair.2:ℝ)+1) (idx.unpair.2+1)
      (1/((idx.unpair.2:ℝ)+1)) (by positivity) (by positivity) (by positivity) (by positivity)
      w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX (hZ t) hQ0 (hSize t) hWM hM hMs
      hL hsm hWL hML hLexact (hXL t) (pattern t) face.2.1 face.2.2
      (g t) (x t) (b0 t) (b1 t) (qval t) (hQ t)
  have hOneBad (face : Face) (idx : ℕ) :
      Tendsto (fun N=>μ N (OneBad N face idx)) atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal (hOneBadReal face idx)
    have heq : (fun N=>ENNReal.ofReal ((μ N).real (OneBad N face idx))) =
        (fun N=>μ N (OneBad N face idx)) := by
      funext N
      exact MeasureTheory.ofReal_measureReal (measure_lt_top (μ N) (OneBad N face idx)).ne
    rw [heq,ENNReal.ofReal_zero] at hh
    exact hh
  let Bad (N idx : ℕ) : Set ((Fin a→ℕ)×ℕ) := ⋃ face : Face,OneBad N face idx
  have hBad (idx : ℕ) : Tendsto (fun N=>μ N (Bad N idx)) atTop (𝓝 0) := by
    have hh : Tendsto (fun N=>∑ face : Face,μ N (OneBad N face idx)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun face _=>hOneBad face idx)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun _=>bot_le) (fun N=>measure_iUnion_fintype_le (μ N) (fun face=>OneBad N face idx))
  let err : ℕ→ℕ→((Fin a→ℕ)×ℕ)→ℝ := fun N idx z=>if z∈Bad N idx then 1 else 0
  have herr (idx : ℕ) (δ : ℝ) (hδ : 0<δ) :
      Tendsto (fun N=>μ N {z | δ≤|err N idx z|}) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hBad idx)
      (fun _=>bot_le) (fun N=>measure_mono ?_)
    intro z hz
    by_contra hn
    have : δ≤(0:ℝ) := by simpa [err,hn] using hz
    exact (not_le_of_gt hδ) this
  obtain ⟨φ,hφ,z,hz,he⟩ := ConditionalDiagonal.select (fun _=>(Fin a→ℕ)×ℕ) μ E' err ε hε hE' herr
  refine ⟨φ,hφ,z,hz,?_⟩
  intro t e j d hd b
  have hh := (he (Nat.pair (d-1) b)).eventually_lt_const (show (0:ℝ)<1 by norm_num)
  filter_upwards [hh] with k hk
  have hn : z k∉Bad (φ k) (Nat.pair (d-1) b) := by
    intro hin
    have : (1:ℝ)<1 := by simp [err,hin] at hk
    exact (lt_irrefl (1:ℝ)) this
  have hnOne : z k∉OneBad (φ k) ⟨t,(e,j)⟩ (Nat.pair (d-1) b) := fun hin=>
    hn (Set.mem_iUnion.mpr ⟨⟨t,(e,j)⟩,hin⟩)
  simpa only [OneBad,Set.mem_ofPred_eq,Nat.unpair_pair,show d-1+1=d by omega] using hnOne

end RoughArrayFace
end

noncomputable section
namespace RoughArrayCoordinates
open RationalLattice RoughFaceShift RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval Filter
open scoped BigOperators Topology
 

theorem physical_grid_continuous {G : Type} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) [MetricSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v : ℕ) (Z : ℕ→ℝ) (hZ : ∀ N,0≤Z N) (d : ℕ)
    (K : ℕ→Fin v→ℤ) (P : ℕ→(Fin (m+v)→ℝ)→G)
    (σ : ℕ→(G⧸Γ)→(G⧸Γ)) (t : ℕ→Fin m→ℤ)
    (hgrid : ∀ b : ℕ,∀ᶠ N in atTop,
      ¬badPhysical Γ m v (1/((b:ℝ)+1)) ((b:ℝ)+1) (b+1)
        (1/((b:ℝ)+1)) (Z N) d (K N) (P N) (σ N) (t N))
    (c₀ C₀ : ℝ) (hc₀ : 0<c₀) (hC₀ : 0<C₀)
    (lo hi : ℕ→Fin v→ℝ) (res : ℕ→Fin v→ℤ)
    (hbox : ∀ᶠ N in atTop,(∀ i,c₀*Z N≤hi N i-lo N i) ∧
      (∀ i,-C₀*Z N≤lo N i ∧ hi N i≤C₀*Z N))
    (F : C(G⧸Γ,ℂ)) :
    Tendsto (fun N=>mean (physicalResidueBox (lo N) (hi N) (res N) d)
      (fun b=>F (σ N (QuotientGroup.mk (P N (Fin.append (fun j=>(t N j:ℝ))
        (fun i=>(affine (K N) (∏ j,t N j) b i:ℝ)))))))-
    mean (physicalResidueBox (lo N) (hi N) (res N) d)
      (fun b=>F (QuotientGroup.mk (P N (Fin.append (fun j=>(t N j:ℝ))
        (fun i=>(affine (K N) (∏ j,t N j) b i:ℝ))))))) atTop (𝓝 0)
 := by
  classical
  have hF := F.continuous
  have hc : @CompactSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) := inferInstance
  let : TopologicalSpace (G⧸Γ) := (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace
  let : CompactSpace (G⧸Γ) := by
    change @CompactSpace (G⧸Γ) (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace
    rw [htop]
    exact hc
  let ftest : C(G⧸Γ,ℂ) := ⟨F,by
    change @Continuous _ _ (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace _ F
    rw [htop]
    exact hF⟩
  let T (N : ℕ) := physicalResidueBox (lo N) (hi N) (res N) d
  let y (N : ℕ) (b : Fin v→ℤ) : G⧸Γ := QuotientGroup.mk (P N
    (Fin.append (fun j=>(t N j:ℝ)) (fun i=>(affine (K N) (∏ j,t N j) b i:ℝ))))
  let E (N : ℕ) : C(G⧸Γ,ℂ)→ₗ[ℂ]ℂ := {
    toFun := fun f=>mean (T N) (fun b=>f (σ N (y N b)))-mean (T N) (fun b=>f (y N b))
    map_add' := by
      intro f g
      simp only [ContinuousMap.add_apply,mean,Finset.sum_add_distrib,mul_add]
      ring
    map_smul' := by
      intro a f
      simp only [ContinuousMap.smul_apply,mean,smul_eq_mul,←Finset.mul_sum,
        RingHom.id_apply]
      ring }
  have hE (N : ℕ) (f : C(G⧸Γ,ℂ)) : ‖E N f‖≤2*‖f‖ := by
    have h₁ := norm_mean_le (T N) (fun b=>f (σ N (y N b))) ‖f‖ (norm_nonneg _)
      (fun b _=>f.norm_coe_le_norm _)
    have h₂ := norm_mean_le (T N) (fun b=>f (y N b)) ‖f‖ (norm_nonneg _)
      (fun b _=>f.norm_coe_le_norm _)
    exact (norm_sub_le _ _).trans (by linarith only [h₁,h₂])
  change Tendsto (fun N=>E N ftest) atTop (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S,hS,η,hη,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction (Y:=G⧸Γ)
    ({ftest} : Set C(G⧸Γ,ℂ)) (by exact isCompact_singleton) ε 2 hε (by norm_num)
  obtain ⟨b,hb⟩ := exists_nat_gt (max (1/c₀) (max C₀ (1/η)))
  have hbc : 1/c₀<(b:ℝ) := (le_max_left _ _).trans_lt hb
  have hbC : C₀<(b:ℝ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hb
  have hbη : 1/η<(b:ℝ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hb
  have hbp : (0:ℝ)<b+1 := by positivity
  have hsmall : 1/((b:ℝ)+1)≤c₀ := by
    rw [div_le_iff₀ hbp]
    have hh := (div_lt_iff₀ hc₀).mp hbc
    nlinarith
  have hηsmall : 1/((b:ℝ)+1)<η := by
    rw [div_lt_iff₀ hbp]
    have hh := (div_lt_iff₀ hη).mp hbη
    nlinarith
  filter_upwards [hgrid b,hbox] with N hgood hgeom
  have hunit (f : C(G⧸Γ,ℂ)) (hf : LipschitzWith 1 f) (hfn : ‖f‖≤1) : ‖E N f‖<η := by
    have hbound : ‖E N f‖<1/((b:ℝ)+1) := by
      by_contra he
      apply hgood
      refine ⟨lo N,hi N,res N,f,?_,?_,?_,?_,le_of_not_gt he⟩
      · intro i
        exact (mul_le_mul_of_nonneg_right hsmall (hZ N)).trans (hgeom.1 i)
      · intro i
        constructor
        · have hh := mul_le_mul_of_nonneg_right (show C₀≤(b:ℝ)+1 by linarith) (hZ N)
          linarith [(hgeom.2 i).1]
        · exact (hgeom.2 i).2.trans (mul_le_mul_of_nonneg_right (by linarith) (hZ N))
      · exact hf.weaken (by exact_mod_cast (show (1:ℕ)≤b+1 by omega))
      · intro x
        have hh := (f.norm_coe_le_norm x).trans hfn
        change ‖f x‖≤((b:ℝ)+1)
        linarith [Nat.cast_nonneg (α:=ℝ) b]
    exact hbound.trans hηsmall
  rw [dist_zero_right]
  by_contra he
  obtain ⟨f,hf,hdisc⟩ := htest (E N) (hE N) ⟨ftest,Set.mem_singleton ftest,le_of_not_gt he⟩
  exact (not_le_of_gt (hunit f (hS f hf).1 (hS f hf).2)) hdisc

end RoughArrayCoordinates

end

end OAI
