import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughArray01
import OAI.Combinatorics.SumProduct.Alignment.RoughTopological03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

noncomputable section
open scoped BigOperators
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)

variable (Γ : ∀ i,Subgroup (G i))

 

omit [Fintype ι] in
theorem source_face_translation {m v : ℕ} (pattern : ι→Fin v→ℤ) (g x : ∀ i,G i)
    (b0 b1 : ι→ℝ) (a0 a1 : Fin q→ℝ) (e : Fin q) (j : Fin v)
    (t : Fin m→ℝ) (z : Fin v→ℝ) (δ : ℝ) (hδ : δ=a0 e+a1 e*∏ k,t k) :
    faceAction G n q c hsk A w hA Γ pattern e j
      (QuotientGroup.mk (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 (Fin.append t z)))=
    QuotientGroup.mk (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1
      (Fin.append t (fun k=>z k+(Pi.single j δ : Fin v→ℝ) k))) := by
  apply congrArg QuotientGroup.mk
  funext i
  apply Subtype.ext
  funext u
  change (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 (Fin.append t z) i).val
      (u+(fun k=>(inputShift q pattern e j i k:ℝ)))=
    (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1
      (Fin.append t (fun k=>z k+(Pi.single j δ : Fin v→ℝ) k)) i).val u
  dsimp only [sourceState,PolynomialArrays.sourceElement]
  simp only [Fin.append_left,Fin.append_right]
  apply congrArg (fun r=>realPower (c i) (g i) r*x i)
  simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  have hleft : (∑ k : Fin q,(a0 k+a1 k*∏ l,t l)*(inputShift q pattern e j i k:ℝ))=
      (a0 e+a1 e*∏ l,t l)*(pattern i j:ℝ) := by
    simp [inputShift,Pi.single_apply]
  have hright : (∑ k : Fin v,(pattern i k:ℝ)*(Pi.single j δ : Fin v→ℝ) k)=(pattern i j:ℝ)*δ := by
    simp [Pi.single_apply]
  rw [hleft,hright,hδ]
  ring

end RoughArrayFace
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (Γ : ∀ i,Subgroup (G i))

 

def actualData {m v : ℕ} (pattern : ι→Fin v→ℤ) (g x : ∀ i,G i)
    (b0 b1 : ι→ℝ) (a0 a1 : Fin q→ℝ) (e : Fin q) (j : Fin v)
    (origin : Fin v→ℤ) (δ : (Fin m→ℤ)→ℤ) :
    FaceData m v (Carrier G n q c hsk A w hA) (lattice G n q c hsk A w hA Γ) where
  A:=origin
  P:=sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1
  σ:=faceAction G n q c hsk A w hA Γ pattern e j
  h:=fun t=>Pi.single j (δ t)
end RoughArrayFace
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace
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
 

theorem source_raw_array_own_face_decay
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    [MetricSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)]
    (htop : (inferInstance : MetricSpace
      ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice G n q c hsk A w hA Γ))
    (m v d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (R H : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j,(X N j:ℝ)^2)^a) atTop atTop)
    (hH : ∀ N,0≤H N) (hHZ : Tendsto (fun N=>H N/(R N/(M N:ℝ))) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N)
    (hXL : ∀ j,Tendsto (fun N=>(X N j:ℝ)/(L N:ℝ)) atTop atTop)
    (pattern : ι→Fin v→ℤ) (e : Fin q) (j : Fin v)
    (g x : ℕ→Label m→∀ i,G i) (b0 b1 : ℕ→Label m→ι→ℝ)
    (a0 a1 : ℕ→Label m→Fin q→ℝ) (origin : ℕ→Label m→Fin v→ℤ)
    (δ : ℕ→Label m→(Fin m→ℤ)→ℤ)
    (hδ : ∀ N b,b∈(fullDomain (X N) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) → Good (X N) (Xp N) (R N) b →
      ∀ t∈productTimes b.scales b.residue (L N),
        (δ N b t:ℝ)=a0 N b e+a1 N b e*∏ l,(t l:ℝ) ∧
        (d:ℤ)∣δ N b t ∧ |(δ N b t:ℝ)|≤H N) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)).real (rawFaceEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N b) (x N b)
          (b0 N b) (b1 N b) (a0 N b) (a1 N b) e j (origin N b) (δ N b))))
      atTop (𝓝 0)
 := by
  obtain ⟨chart,grid,hgridpos,hgrid,J,hJ,hdegree⟩:=
    source_joint_geometry G n q c hsk A w hA hw Γ hΓ
  apply source_raw_continuous_face_grid_decay (lattice G n q c hsk A w hA Γ)
    chart grid hgridpos hgrid htop m v (J*(m+1)) d hd c₀ C₀ B η hc₀ hC₀ hB hη
    w0 M Xp X R H L hw0 hX hXp hXt hXpt hR hRX hZ hH hHZ hWM hM hMs hL hsm hWL hXL
    (faceAction G n q c hsk A w hA Γ pattern e j)
  intro N b hb hg
  refine ⟨?_,rfl,?_,?_⟩
  · exact hdegree m v pattern (g N b) (x N b) (b0 N b) (b1 N b) (a0 N b) (a1 N b)
  · intro t ht i
    obtain ⟨_,hdiv,hbound⟩:=hδ N b hb hg t ht
    change (d:ℤ)∣(Pi.single j (δ N b t) : Fin v→ℤ) i ∧
      |((Pi.single j (δ N b t) : Fin v→ℤ) i:ℝ)|≤H N
    by_cases hij:i=j
    · subst i;simp only [Pi.single_eq_same];exact ⟨hdiv,hbound⟩
    · simp only [Pi.single_eq_of_ne hij,Int.cast_zero,abs_zero]
      exact ⟨dvd_zero _,hH N⟩
  · intro t ht z
    obtain ⟨hslope,_,_⟩:=hδ N b hb hg t ht
    have HH:=source_face_translation G n q c hsk A w hA hw Γ pattern (g N b) (x N b)
      (b0 N b) (b1 N b) (a0 N b) (a1 N b) e j (fun l=>(t l:ℝ))
      (fun i=>(z i:ℝ)) (δ N b t:ℝ) hslope
    have hcast : (fun i=>(z i:ℝ)+(Pi.single j (δ N b t:ℝ):Fin v→ℝ) i)=
        (fun i=>((z i+(Pi.single j (δ N b t):Fin v→ℤ) i:ℤ):ℝ)) := by
      funext i
      by_cases hij:i=j
      · subst i;simp
      · simp [Pi.single_eq_of_ne hij]
    rw [hcast] at HH
    exact HH

end RoughArrayFace
end

noncomputable section
namespace RoughArrayCoordinates
open RationalLattice MalcevCharacters RoughFaceShift RoughArrayFace
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators

def affine {v : ℕ} (K : Fin v→ℤ) (t : ℤ) (b : Fin v→ℤ) : Fin v→ℤ := fun j=>K j+t*b j

def endpoint {v : ℕ} (K : Fin v→ℤ) (t : ℤ) (lo : Fin v→ℝ) : Fin v→ℝ :=
  fun j=>(K j:ℝ)+(t:ℝ)*lo j

end RoughArrayCoordinates
end

noncomputable section
namespace RoughArrayCoordinates
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators

lemma coordinate_injective {v : ℕ} (K : Fin v→ℤ) {t : ℤ} (ht : 0<t) :
    Function.Injective (affine K t) := by
  intro b b' he
  funext i
  have HH:=congrFun he i
  dsimp [affine] at HH
  exact (mul_left_cancel₀ (ne_of_gt ht)) (add_left_cancel HH)

lemma mem_physical {v : ℕ} (lo hi : Fin v→ℝ) (res : Fin v→ℤ) (d : ℕ) (x : Fin v→ℤ) :
    x∈physicalResidueBox lo hi res d ↔
      (∀ i,lo i≤(x i:ℝ) ∧ (x i:ℝ)<hi i) ∧ ∀ i,x i≡res i [ZMOD d] := by
  classical
  simp only [physicalResidueBox,Finset.mem_filter,mem_boxIndices _ _ _ _ zero_lt_one,zero_add,one_mul]

lemma affine_residue_iff (K t b res : ℤ) (d : ℕ) (hdt : IsCoprime (d:ℤ) t) :
    K+t*b≡K+t*res [ZMOD d] ↔ b≡res [ZMOD d] := by
  rw [Int.modEq_iff_dvd,Int.modEq_iff_dvd]
  have he : K+t*res-(K+t*b)=t*(res-b) := by ring
  rw [he]
  exact ⟨hdt.dvd_of_dvd_mul_left,fun h=>dvd_mul_of_dvd_right h _⟩

lemma physical_image {v : ℕ} (K A res : Fin v→ℤ) (t : ℤ) (ht : 0<t)
    (d M : ℕ) (hdt : IsCoprime (d:ℤ) t) (hMt : IsCoprime (M:ℤ) t)
    (hK : ∀ j,t∣(M:ℤ)*K j+A j) (lo hi : Fin v→ℝ) :
    (physicalResidueBox lo hi res d).image (affine K t)=
      nestedBox (endpoint K t lo) (endpoint K t hi) (affine K t res) A d M t := by
  classical
  have htr : (0:ℝ)<t := by exact_mod_cast ht
  ext x
  simp only [nestedBox,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨hb,hres⟩:=(mem_physical _ _ _ _ _).mp hb
    refine ⟨(mem_physical _ _ _ _ _).mpr ⟨?_,?_⟩,?_⟩
    · intro i
      dsimp [endpoint,affine]
      push_cast
      constructor <;> nlinarith [(hb i).1,(hb i).2]
    · intro i
      exact (affine_residue_iff _ _ _ _ _ hdt).mpr (hres i)
    · intro i
      have he : (M:ℤ)*(K i+t*b i)+A i=((M:ℤ)*K i+A i)+t*((M:ℤ)*b i) := by ring
      dsimp [affine]
      rw [he]
      exact dvd_add (hK i) (dvd_mul_right _ _)
  · rintro ⟨hx,hdiv⟩
    obtain ⟨hx,hres⟩:=(mem_physical _ _ _ _ _).mp hx
    have hxb (i : Fin v) : ∃ b : ℤ,x i=K i+t*b := by
      have hh:=dvd_sub (hdiv i) (hK i)
      have he : (M:ℤ)*x i+A i-((M:ℤ)*K i+A i)=(M:ℤ)*(x i-K i) := by ring
      rw [he] at hh
      obtain ⟨b,hb⟩:=hMt.symm.dvd_of_dvd_mul_left hh
      exact ⟨b,by linarith⟩
    choose b hb using hxb
    have he : affine K t b=x := by funext i;exact (hb i).symm
    refine ⟨b,(mem_physical _ _ _ _ _).mpr ⟨?_,?_⟩,he⟩
    · intro i
      have HH:=hx i
      rw [hb i] at HH
      dsimp [endpoint] at HH
      push_cast at HH
      constructor <;> nlinarith [HH.1,HH.2]
    · intro i
      have HH:=hres i
      rw [hb i] at HH
      exact (affine_residue_iff _ _ _ _ _ hdt).mp HH
 

theorem mean_affine_nested {v : ℕ} (K A res : Fin v→ℤ) (t : ℤ) (ht : 0<t)
    (d M : ℕ) (hdt : IsCoprime (d:ℤ) t) (hMt : IsCoprime (M:ℤ) t)
    (hK : ∀ j,t∣(M:ℤ)*K j+A j) (lo hi : Fin v→ℝ) (f : (Fin v→ℤ)→ℂ) :
    mean (physicalResidueBox lo hi res d) (fun b=>f (affine K t b))=
      mean (nestedBox (endpoint K t lo) (endpoint K t hi) (affine K t res) A d M t) f
 := by
  classical
  rw [← physical_image K A res t ht d M hdt hMt hK lo hi]
  exact (mean_image _ _ (coordinate_injective K ht) f).symm

end RoughArrayCoordinates

end

end OAI
