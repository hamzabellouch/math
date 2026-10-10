import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ResidueAlignment01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

noncomputable section
namespace ProductExposureLaw
open MeasureTheory ProductExposureLabels RawHarmonicProbability
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

def outsideDomain {h : ℕ} (X : Fin h→ℕ) (W : ℕ) : Finset (Fin h→ℕ) :=
  Fintype.piFinset (fun j=>units (X j) W)

def outsideLaw {h : ℕ} (X : Fin h→ℕ) (W : ℕ) (hW : 0<W) (hX : ∀ j,4*W≤X j) :
    Measure (Fin h→ℕ) := Measure.pi (fun j=>(law (X j) W hW (hX j):Measure ℕ))

instance outsideLaw_probability {h : ℕ} (X : Fin h→ℕ) (W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) : IsProbabilityMeasure (outsideLaw X W hW hX) := by
  unfold outsideLaw
  infer_instance

def reassemble {m h n : ℕ} (e : Fin (m+h)≃Fin n)
    (y : Fin h→ℕ) (z : (Fin m→ℕ)×ℕ) : (Fin n→ℕ)×ℕ :=
  (fun j=>Fin.append z.1 y (e.symm j),z.2)
lemma outside_ae_domain {h : ℕ} (X : Fin h→ℕ) (W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) : ∀ᵐ y ∂outsideLaw X W hW hX,y∈outsideDomain X W := by
  have hh (j : Fin h) : ∀ᵐ y ∂outsideLaw X W hW hX,y j∈units (X j) W :=
    (measurePreserving_eval (fun j=>(law (X j) W hW (hX j):Measure ℕ)) j).quasiMeasurePreserving.ae
      (law_ae_units (X j) W hW (hX j))
  filter_upwards [ae_all_iff.mpr hh] with y hy
  exact Fintype.mem_piFinset.mpr hy

lemma outside_weights_sum {h : ℕ} (X : Fin h→ℕ) (W : ℕ) (hW : 0<W)
    (hX : ∀ j,4*W≤X j) :
    ∑ y∈outsideDomain X W,(outsideLaw X W hW hX).real {y}=1 := by
  rw [sum_measureReal_singleton]
  have hh : (outsideLaw X W hW hX).real (outsideDomain X W:Set _) =
      (outsideLaw X W hW hX).real Set.univ := by
    apply measureReal_congr
    filter_upwards [outside_ae_domain X W hW hX] with y hy
    change (y∈outsideDomain X W)=(y∈(Set.univ : Set (Fin h→ℕ)))
    exact propext ⟨fun _=>Set.mem_univ _,fun _=>hy⟩
  simpa using hh

lemma joint_reassemble {m h n : ℕ} (e : Fin (m+h)≃Fin n)
    (X : Fin n→ℕ) (Xp W : ℕ) (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) :
    Measure.map (fun yz=>reassemble e yz.1 yz.2)
      ((outsideLaw (fun j : Fin h=>X (e (j.natAdd m))) W hW (fun _=>hX _)).prod
        (jointLaw (fun j : Fin m=>X (e (j.castAdd h))) Xp W hW (fun _=>hX _) hXp)) =
      jointLaw X Xp W hW hX hXp := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun yz=>reassemble e yz.1 yz.2) ⁻¹' {z} =
      {fun j : Fin h=>z.1 (e (j.natAdd m))} ×ˢ
        {(fun j : Fin m=>z.1 (e (j.castAdd h)),z.2)} := by
    ext yz
    constructor
    · intro hy
      change reassemble e yz.1 yz.2=z at hy
      have h1 := congrArg Prod.fst hy
      have h2 := congrArg Prod.snd hy
      refine ⟨?_,?_⟩
      · apply funext
        intro j
        have hh := congrFun h1 (e (j.natAdd m))
        simpa [reassemble] using hh
      · apply Prod.ext
        · apply funext
          intro j
          have hh := congrFun h1 (e (j.castAdd h))
          simpa [reassemble] using hh
        · exact h2
    · rintro ⟨hy,hz⟩
      change yz.1=(fun j : Fin h=>z.1 (e (j.natAdd m))) at hy
      change yz.2=(fun j : Fin m=>z.1 (e (j.castAdd h)),z.2) at hz
      change reassemble e yz.1 yz.2=z
      rw [hy,hz]
      apply Prod.ext
      · funext j
        rcases e.surjective j with ⟨i,rfl⟩
        refine Fin.addCases ?_ ?_ i
        · intro a
          simp [reassemble]
        · intro a
          simp [reassemble]
      · rfl
  rw [he,Measure.prod_prod]
  change _ = (jointLaw X Xp W hW hX hXp) {(z.1,z.2)}
  simp only [outsideLaw,jointLaw,←Set.singleton_prod_singleton,Measure.prod_prod,Measure.pi_singleton]
  rw [mul_left_comm,←mul_assoc]
  congr 1
  calc
    _ = ∏ i : Fin (m+h),(law (X (e i)) W hW (hX (e i)):Measure ℕ) {z.1 (e i)} := by
      simpa using (Fin.prod_univ_add (fun i : Fin (m+h)=>
        (law (X (e i)) W hW (hX (e i)):Measure ℕ) {z.1 (e i)})).symm
    _ = _ := e.prod_comp (fun j=>(law (X j) W hW (hX j):Measure ℕ) {z.1 j})
 

theorem joint_outside_disintegration {m h n : ℕ} (e : Fin (m+h)≃Fin n)
    (X : Fin n→ℕ) (Xp W : ℕ) (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (E : Set ((Fin n→ℕ)×ℕ)) :
    let Xi := fun j : Fin m=>X (e (j.castAdd h))
    let Xo := fun j : Fin h=>X (e (j.natAdd m))
    (jointLaw X Xp W hW hX hXp).real E =
      ∑ y∈outsideDomain Xo W,(outsideLaw Xo W hW (fun _=>hX _)).real {y} *
        (jointLaw Xi Xp W hW (fun _=>hX _) hXp).real {z | reassemble e y z∈E}
 := by
  classical
  dsimp only
  have hm := joint_reassemble e X Xp W hW hX hXp
  rw [←hm,measureReal_def,Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete,
    Measure.prod_apply MeasurableSet.of_discrete]
  conv_lhs => rw [←Measure.restrict_eq_self_of_ae_mem
    (outside_ae_domain (fun j : Fin h=>X (e (j.natAdd m))) W hW (fun j=>hX _))]
  rw [lintegral_finset,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.toReal_mul,mul_comm]
    rfl
  · intro y hy
    exact ENNReal.mul_ne_top (by finiteness) (by finiteness)

end ProductExposureLaw
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (Γ : ∀ i,Subgroup (G i))
 

theorem source_full_earlier_face_decay
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    [MetricSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)]
    (htop : (inferInstance : MetricSpace
      ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice G n q c hsk A w hA Γ))
    (m h a v d : ℕ) (perm : Fin (m+h)≃Fin a) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j : Fin m,(X N (perm (j.castAdd h)):ℝ)^2)^a) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : Tendsto (fun N=>(Q N+(∏ l : Fin m,(X N (perm (l.castAdd h)):ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N)
    (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ j : Fin m,Tendsto (fun N=>(X N (perm (j.castAdd h)):ℝ)/(L N:ℝ)) atTop atTop)
    (pattern : ι→Fin (v+1)→ℤ) (e : Fin q) (j : Fin (v+1))
    (g x : ℕ→(Fin h→ℕ)→Label m→∀ i,G i) (b0 b1 : ℕ→(Fin h→ℕ)→Label m→ι→ℝ)
    (qval : ℕ→(Fin h→ℕ)→Label m→Fin q→ℤ)
    (hQ : ∀ N y,y∈outsideDomain (fun l : Fin h=>X N (perm (l.natAdd m))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin m=>X N (perm (l.castAdd h))) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval N y b k:ℝ)|≤Q N) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)).real {z |
      let y := fun l : Fin h=>z.1 (perm (l.natAdd m))
      (fun l : Fin m=>z.1 (perm (l.castAdd h)),z.2)∈
      rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N y b) (x N y b)
          (b0 N y b) (b1 N y b) (fun k=>(qval N y b k:ℝ)/(M N:ℝ))
          (fun k=>-(residueData (L N) (qval N y b k) b:ℝ)/(M N:ℝ)) e j
          (coarseOrigin v (M N) (R N) b) (shift (M N) (L N) (qval N y b e) b))})
      atTop (𝓝 0)
 := by
  classical
  let Xo (N : ℕ) (l : Fin h) := X N (perm (l.natAdd m))
  let Xi (N : ℕ) (l : Fin m) := X N (perm (l.castAdd h))
  let κ (N : ℕ) := ↥(outsideDomain (Xo N) (primorial (w0 N)))
  let p (N : ℕ) (y : κ N) :=
    (outsideLaw (Xo N) (primorial (w0 N)) (primorial_pos _) (fun l=>hX N _)).real {y.val}
  have hsum (N : ℕ) (f : (Fin h→ℕ)→ℝ) :
      ∑ y : κ N,f y.val = ∑ y∈outsideDomain (Xo N) (primorial (w0 N)),f y := by
    exact (Finset.sum_subtype _ (fun _=>Iff.rfl) f).symm
  have hp (N : ℕ) (y : κ N) : 0≤p N y := measureReal_nonneg
  have hmass (N : ℕ) : ∑ y,p N y=1 := by
    dsimp only [p]
    exact (hsum N (fun y=>(outsideLaw (Xo N) (primorial (w0 N))
      (primorial_pos _) (fun l=>hX N _)).real {y})).trans
      (outside_weights_sum (Xo N) (primorial (w0 N)) (primorial_pos _) (fun l=>hX N _))
  have hh := source_outside_conditioning_face_decay G n q c hsk A w hA hw Γ hΓ htop
    m v d hd c₀ C₀ B η hc₀ hC₀ hB hη w0 M Xp Xi R Q L hw0 (fun N l=>hX N _) hXp
    (fun l=>hXt _) hXpt hR hRX hZ hQ0 hSize hWM hM hMs hL hsm hWL hML hLexact hXL
    pattern e j κ p hp hmass (fun N y=>g N y.val) (fun N y=>x N y.val)
    (fun N y=>b0 N y.val) (fun N y=>b1 N y.val) (fun N y=>qval N y.val)
    (fun N y=>hQ N y.val y.property)
  apply hh.congr' (Eventually.of_forall (fun N=>?_))
  rw [joint_outside_disintegration perm]
  dsimp only [p]
  rw [hsum N (fun y=>(outsideLaw (Xo N) (primorial (w0 N))
    (primorial_pos _) (fun l=>hX N _)).real {y} *
    (jointLaw (Xi N) (Xp N) (primorial (w0 N)) (primorial_pos _) (fun l=>hX N _) (hXp N)).real
      (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N y b) (x N y b)
          (b0 N y b) (b1 N y b) (fun k=>(qval N y b k:ℝ)/(M N:ℝ))
          (fun k=>-(residueData (L N) (qval N y b k) b:ℝ)/(M N:ℝ)) e j
          (coarseOrigin v (M N) (R N) b) (shift (M N) (L N) (qval N y b e) b))))]
  apply Finset.sum_congr rfl
  intro y hy
  congr 2
  ext z
  simp only [Set.mem_ofPred_eq,reassemble,Equiv.symm_apply_apply,Fin.append_left,Fin.append_right]

end RoughArrayFace
end

 

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace ConditionalDiagonal
variable (Ω : ℕ → Type) [∀ N,MeasurableSpace (Ω N)]
variable (μ : ∀ N,Measure (Ω N)) (A : ∀ N,Set (Ω N))
variable (E : ∀ N,ℕ → Ω N → ℝ) (ε : ℝ≥0∞) (hε : 0<ε)
variable (hA : ∀ N,ε≤μ N (A N))
variable (hE : ∀ i δ,0<δ → Tendsto
  (fun N=>μ N {x | δ≤|E N i x|}) atTop (𝓝 0))

include hε hA hE in
 

theorem select : ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ x : ∀ k,Ω (φ k),
    (∀ k,x k∈A (φ k)) ∧ ∀ i,Tendsto (fun k=>E (φ k) i (x k)) atTop (𝓝 0) := by
  classical
  have hev (k : ℕ) : ∀ᶠ N in atTop,∃ x∈A N,∀ i≤k,|E N i x|<1/((k:ℝ)+1) := by
    let δ : ℝ:=1/((k:ℝ)+1)
    have hδ : 0<δ := by dsimp [δ]; positivity
    have ht : Tendsto (fun N=>∑ i∈Finset.range (k+1),μ N {x | δ≤|E N i x|})
        atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using
        (tendsto_finsetSum (Finset.range (k+1)) (fun i _=>hE i δ hδ))
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN
    let Bad : Set (Ω N):=⋃ i∈Finset.range (k+1),{x | δ≤|E N i x|}
    have hm : μ N Bad<μ N (A N) :=
      (measure_biUnion_finset_le (Finset.range (k+1)) _).trans_lt (hN.trans_le (hA N))
    have hn : ¬A N⊆Bad := fun h=>not_lt_of_ge (measure_mono h) hm
    obtain ⟨x,hx,hxb⟩:=Set.not_subset.mp hn
    refine ⟨x,hx,?_⟩
    intro i hi
    by_contra! h
    exact hxb (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),h⟩⟩)
  have hth (k : ℕ) : ∃ T : ℕ,∀ N≥T,∃ x∈A N,∀ i≤k,|E N i x|<1/((k:ℝ)+1) :=
    Filter.eventually_atTop.mp (hev k)
  choose T hT using hth
  let φ (k : ℕ):=k+∑ j∈Finset.range (k+1),T j
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [φ,Finset.sum_range_succ]
    omega
  have hφT (k : ℕ) : T k≤φ k := by
    have hsum : T k≤∑ j∈Finset.range (k+1),T j :=
      Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    exact hsum.trans (Nat.le_add_left _ _)
  choose x hx hxe using (fun k=>hT k (φ k) (hφT k))
  refine ⟨φ,hφ,x,hx,?_⟩
  intro i
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have ht : ∀ᶠ k : ℕ in atTop,1/((k:ℝ)+1)<δ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩:=Filter.eventually_atTop.mp ht
  refine ⟨max N i,?_⟩
  intro k hk
  simpa only [Real.dist_eq,sub_zero] using
    (hxe k i ((le_max_right N i).trans hk)).trans (hN k ((le_max_left N i).trans hk))

end ConditionalDiagonal

end

end OAI
