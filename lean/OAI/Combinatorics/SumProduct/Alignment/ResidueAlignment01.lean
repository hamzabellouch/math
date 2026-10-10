import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerAlignment01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
namespace SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators

 

def residue (L t q : ℤ) : ℤ :=
  if h : 0<L ∧ IsCoprime t L then
    Classical.choose (IntegerAlignment.residue_shift (M:=L) (W:=1) (t:=t) (q:=q) (w:=1)
      h.1 (by norm_num) (by omega) (by simpa using h.2) (one_dvd q))
  else 0

def residueData {m : ℕ} (L : ℤ) (q : ℤ) (b : Label m) : ℤ :=
  residue L (∏ j,b.residue j) q

def shift {m : ℕ} (M : ℕ) (L q : ℤ) (b : Label m) (t : Fin m→ℤ) : ℤ :=
  (q-(∏ j,t j)*residueData L q b)/(M:ℤ)
end SourceResidueAlignment
end

noncomputable section
namespace SourceResidueAlignment
open ProductExposureLabels ProductExposureLaw RoughFaceShift RoughProductRemoval RoughSourceExceptional RoughScales
open scoped BigOperators

lemma residue_spec (L t q : ℤ) (hL : 0<L) (ht : IsCoprime t L) :
    0≤residue L t q ∧ residue L t q<L ∧ t*residue L t q ≡ q [ZMOD L] := by
  have hh:=Classical.choose_spec (IntegerAlignment.residue_shift (M:=L) (W:=1) (t:=t) (q:=q) (w:=1)
    hL (by norm_num) (by omega) (by simpa using ht) (one_dvd q))
  obtain ⟨Δ,h1,h2,h3,hrest⟩:=hh
  dsimp [residue]
  rw [dite_eq_left ⟨hL,ht⟩]
  exact ⟨h1,by simpa using h2,by simpa using h3⟩

lemma shift_spec {m : ℕ} (w M d : ℕ) (hM : 0<M) (hd : 0<d) (hdw : d≤w)
    (L : ℤ) (hL : 0<L) (hLexact : L=(M:ℤ)*(primorial w:ℤ)^w)
    (hLs : Smooth w L) (b : Label m) (hr : ∀ j,(b.residue j).natAbs.Coprime (primorial w))
    (X : Fin m→ℕ) (hX : ∀ j,2*b.scales j≤(X j:ℝ)^2)
    (q : ℤ) (Q : ℝ) (hQ : |(q:ℝ)|≤Q)
    (t : Fin m→ℤ) (ht : t∈productTimes b.scales b.residue L) :
    (shift M L q b t:ℝ)=(q:ℝ)/(M:ℝ)+(-(residueData L q b:ℝ)/(M:ℝ))*(∏ j,(t j:ℝ)) ∧
      (d:ℤ)∣shift M L q b t ∧
      |(shift M L q b t:ℝ)|≤(Q+(∏ j,(X j:ℝ)^2)*(L:ℝ))/(M:ℝ) := by
  have hcop : IsCoprime (∏ j,b.residue j) L := IsCoprime.prod_left
    (fun j _=>(coprime_smooth_rough hLs ((rough_iff_coprime _ _).mpr (hr j))).symm)
  have hres:=residue_spec L (∏ j,b.residue j) q hL hcop
  change 0≤residueData L q b ∧ residueData L q b<L ∧
    (∏ j,b.residue j)*residueData L q b ≡ q [ZMOD L] at hres
  have htt (j : Fin m) := (mem_times (b.scales j) (b.residue j) L (t j) hL).mp
    (Fintype.mem_piFinset.mp ht j)
  have hmod : (∏ j,t j) ≡ (∏ j,b.residue j) [ZMOD L] := by
    apply Int.ModEq.prod
    intro j _
    obtain ⟨k,hk⟩:=(htt j).2.2
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-k,?_⟩
    linear_combination -hk
  have hc : L∣q-(∏ j,t j)*residueData L q b :=
    Int.modEq_iff_dvd.mp ((hmod.mul_right _).trans hres.2.2)
  have hML : (M:ℤ)∣L := by rw [hLexact];exact dvd_mul_right _ _
  have hk : (M:ℤ)*shift M L q b t=q-(∏ j,t j)*residueData L q b :=
    Int.mul_ediv_cancel' (hML.trans hc)
  have hkR : (M:ℝ)*(shift M L q b t:ℝ)=(q:ℝ)-(∏ j,(t j:ℝ))*(residueData L q b:ℝ) := by
    exact_mod_cast hk
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hslope : (shift M L q b t:ℝ)=(q:ℝ)/(M:ℝ)+(-(residueData L q b:ℝ)/(M:ℝ))*(∏ j,(t j:ℝ)) := by
    field_simp [hMr.ne']
    linear_combination hkR
  refine ⟨hslope,?_,?_⟩
  · obtain ⟨k,hk'⟩:=hc
    have hδ : shift M L q b t=(primorial w:ℤ)^w*k := by
      unfold shift
      rw [hk',hLexact,mul_assoc,Int.mul_ediv_cancel_left _ (by exact_mod_cast (Nat.ne_of_gt hM))]
    rw [hδ]
    have hdW : (d:ℤ)∣(primorial w:ℤ)^w := by
      exact_mod_cast (IntegerAlignment.fixed_dvd_primorial_pow hd hdw hdw)
    exact dvd_mul_of_dvd_left hdW k
  · have htt0 : ∀ j,(0:ℝ)≤(t j:ℝ) := fun j=>le_trans
      (le_of_lt (pow_pos (by norm_num : (0:ℝ)<2) _)) (htt j).1
    have htu : (∏ j,(t j:ℝ))≤∏ j,(X j:ℝ)^2 :=
      Finset.prod_le_prod₀ (fun j _=>htt0 j) (fun j _=>(htt j).2.1.le.trans (hX j))
    have ht0 : (0:ℝ)≤∏ j,(t j:ℝ) := Finset.prod_nonneg (fun j _=>htt0 j)
    have hr0 : (0:ℝ)≤(residueData L q b:ℝ) := by exact_mod_cast hres.1
    have hrL : (residueData L q b:ℝ)≤(L:ℝ) := by exact_mod_cast hres.2.1.le
    have hmul : (∏ j,(t j:ℝ))*(residueData L q b:ℝ)≤(∏ j,(X j:ℝ)^2)*(L:ℝ) :=
      mul_le_mul htu hrL hr0 (Finset.prod_nonneg (fun j _=>sq_nonneg _))
    have hab := abs_sub (q:ℝ) ((∏ j,(t j:ℝ))*(residueData L q b:ℝ))
    rw [abs_of_nonneg (mul_nonneg ht0 hr0)] at hab
    have hka := congrArg abs hkR
    rw [abs_mul,abs_of_pos hMr] at hka
    apply (le_div_iff₀ hMr).mpr
    nlinarith

end SourceResidueAlignment
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
 

theorem source_residue_physical_array_face_decay
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    [MetricSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)]
    (htop : (inferInstance : MetricSpace
      ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice G n q c hsk A w hA Γ))
    (m v d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j,(X N j:ℝ)^2)^a) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : Tendsto (fun N=>(Q N+(∏ l : Fin m,(X N l:ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N)
    (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ j,Tendsto (fun N=>(X N j:ℝ)/(L N:ℝ)) atTop atTop)
    (pattern : ι→Fin (v+1)→ℤ) (e : Fin q) (j : Fin (v+1))
    (g x : ℕ→Label m→∀ i,G i) (b0 b1 : ℕ→Label m→ι→ℝ)
    (qval : ℕ→Label m→Fin q→ℤ)
    (hQ : ∀ N b,b∈(fullDomain (X N) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval N b k:ℝ)|≤Q N) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)).real (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N b) (x N b)
          (b0 N b) (b1 N b) (fun k=>(qval N b k:ℝ)/(M N:ℝ))
          (fun k=>-(residueData (L N) (qval N b k) b:ℝ)/(M N:ℝ)) e j (coarseOrigin v (M N) (R N) b) (shift (M N) (L N) (qval N b e) b))))
      atTop (𝓝 0)
 := by
  let H : ℕ→ℝ:=fun N=>(Q N+(∏ l : Fin m,(X N l:ℝ)^2)*(L N:ℝ))/(M N:ℝ)
  have hH : ∀ N,0≤H N := by
    intro N
    dsimp [H]
    apply div_nonneg
    · apply add_nonneg (hQ0 N)
      exact mul_nonneg (Finset.prod_nonneg (fun l _=>sq_nonneg _)) (by exact_mod_cast (hL N).le)
    · positivity
  have hHZ : Tendsto (fun N=>H N/(R N/(M N:ℝ))) atTop (𝓝 0) := by
    apply hSize.congr'
    filter_upwards [] with N
    dsimp [H]
    field_simp [show (M N:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt (hM N)),(hR N).ne']
  let a0 : ℕ→Label m→Fin q→ℝ := fun N b k=>if d≤w0 N then (qval N b k:ℝ)/(M N:ℝ) else 0
  let a1 : ℕ→Label m→Fin q→ℝ := fun N b k=>if d≤w0 N then -(residueData (L N) (qval N b k) b:ℝ)/(M N:ℝ) else 0
  let δ : ℕ→Label m→(Fin m→ℤ)→ℤ := fun N b t=>if d≤w0 N then shift (M N) (L N) (qval N b e) b t else 0
  have hδ : ∀ N b,b∈(fullDomain (X N) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) → Good (X N) (Xp N) (R N) b →
      ∀ t∈productTimes b.scales b.residue (L N),
        (δ N b t:ℝ)=a0 N b e+a1 N b e*∏ l,(t l:ℝ) ∧
        (d:ℤ)∣δ N b t ∧ |(δ N b t:ℝ)|≤H N := by
    intro N b hb hg t ht
    by_cases hn:d≤w0 N
    · simp only [a0,a1,δ,ite_eq_left hn]
      have hr:=image_residues (X N) (Xp N) (primorial (w0 N)) (L N) (M N:ℤ) (R N)
        (hL N) (by exact_mod_cast hM N) (hWL N) (hWM N) b hb
      exact shift_spec (w0 N) (M N) d (hM N) hd hn (L N) (hL N) (hLexact N)
        (hsm N) b hr.2.2.1 (X N) (fun l=>(hg.1 l).2) (qval N b e) (Q N) (hQ N b hb e) t ht
    · simp only [a0,a1,δ,ite_eq_right hn,Int.cast_zero,zero_mul,add_zero,abs_zero]
      exact ⟨True.intro,dvd_zero _,hH N⟩
  have hh:=source_raw_physical_array_own_face_decay G n q c hsk A w hA hw Γ hΓ htop
    m v d hd c₀ C₀ B η hc₀ hC₀ hB hη w0 M Xp X R H L hw0 hX hXp hXt hXpt
    hR hRX hZ hH hHZ hWM hM hMs hL hsm hWL hML hXL pattern e j g x b0 b1 a0 a1 δ hδ
  apply hh.congr'
  filter_upwards [hw0.eventually (eventually_ge_atTop d)] with N hn
  simp only [a0,a1,δ,ite_eq_left hn]

end RoughArrayFace
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
 

theorem source_outside_conditioning_face_decay
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    [MetricSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)]
    (htop : (inferInstance : MetricSpace
      ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice G n q c hsk A w hA Γ))
    (m v d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j,(X N j:ℝ)^2)^a) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : Tendsto (fun N=>(Q N+(∏ l : Fin m,(X N l:ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N)
    (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ j,Tendsto (fun N=>(X N j:ℝ)/(L N:ℝ)) atTop atTop)
    (pattern : ι→Fin (v+1)→ℤ) (e : Fin q) (j : Fin (v+1))
    (κ : ℕ→Type) [∀ N,Fintype (κ N)]
    (p : ∀ N,κ N→ℝ) (hp : ∀ N y,0≤p N y) (hmass : ∀ N,∑ y,p N y=1)
    (g x : ∀ N,κ N→Label m→∀ i,G i) (b0 b1 : ∀ N,κ N→Label m→ι→ℝ)
    (qval : ∀ N,κ N→Label m→Fin q→ℤ)
    (hQ : ∀ N y b,b∈(fullDomain (X N) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval N y b k:ℝ)|≤Q N) :
    Tendsto (fun N=>∑ y,p N y * (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)).real (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N y b) (x N y b)
          (b0 N y b) (b1 N y b) (fun k=>(qval N y b k:ℝ)/(M N:ℝ))
          (fun k=>-(residueData (L N) (qval N y b k) b:ℝ)/(M N:ℝ)) e j (coarseOrigin v (M N) (R N) b) (shift (M N) (L N) (qval N y b e) b))))
      atTop (𝓝 0) := by
  classical
  let mass (N : ℕ) (y : κ N) : ℝ :=
    (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real
      (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N y b) (x N y b)
          (b0 N y b) (b1 N y b) (fun k=>(qval N y b k:ℝ)/(M N:ℝ))
          (fun k=>-(residueData (L N) (qval N y b k) b:ℝ)/(M N:ℝ)) e j
          (coarseOrigin v (M N) (R N) b) (shift (M N) (L N) (qval N y b e) b)))
  have hne (N : ℕ) : (Finset.univ : Finset (κ N)).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := hmass N
    rw [he,Finset.sum_empty] at hh
    norm_num at hh
  have hmax (N : ℕ) : ∃ y : κ N,∀ z : κ N,mass N z≤ mass N y := by
    obtain ⟨y,hy,hm⟩ := Finset.exists_max_image Finset.univ (mass N) (hne N)
    exact ⟨y,fun z=>hm z (Finset.mem_univ _)⟩
  choose y hy using hmax
  have hh := source_residue_physical_array_face_decay G n q c hsk A w hA hw Γ hΓ htop
    m v d hd c₀ C₀ B η hc₀ hC₀ hB hη w0 M Xp X R Q L hw0 hX hXp hXt hXpt
    hR hRX hZ hQ0 hSize hWM hM hMs hL hsm hWL hML hLexact hXL pattern e j
    (fun N=>g N (y N)) (fun N=>x N (y N))
    (fun N=>b0 N (y N)) (fun N=>b1 N (y N)) (fun N=>qval N (y N))
    (fun N=>hQ N (y N))
  change Tendsto (fun N=>mass N (y N)) atTop (𝓝 0) at hh
  change Tendsto (fun N=>∑ z,p N z * mass N z) atTop (𝓝 0)
  apply squeeze_zero' (Eventually.of_forall (fun N=>?_)) (Eventually.of_forall (fun N=>?_)) hh
  · exact Finset.sum_nonneg (fun z _=>mul_nonneg (hp N z) (measureReal_nonneg))
  · calc
      ∑ z,p N z * mass N z ≤ ∑ z,p N z * mass N (y N) :=
        Finset.sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (hy N z) (hp N z))
      _ = mass N (y N) := by rw [←Finset.sum_mul,hmass,one_mul]

end RoughArrayFace

end

end OAI
