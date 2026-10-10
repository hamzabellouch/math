import Mathlib
import OAI.Probability.Ballisticity.Crossings.GaussianBadCutoff
import OAI.Probability.Ballisticity.Estimates.CommonBoundaryRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma trueRecord_firstLayerHit {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (X : Path d) (n : ℕ)
    (hn : TrueRecord ℓ X n) : X ∈ FirstLayerHit height (height (X n)) n := by
  refine ⟨rfl,?_⟩
  intro j hj
  have := hn.1 j hj
  rw [hproj,hproj] at this
  exact_mod_cast this

lemma firstCommonLayer_boundaryAt {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (H : ℤ)
    (P : Path d × Path d) (hx : height (P.1 0) < H) (hy : height (P.2 0) < H)
    (n m : ℕ)
    (hn : P.1 ∈ FirstLayerHit height (H+commonOffset ℓ height H P) n)
    (hm : P.2 ∈ FirstLayerHit height (H+commonOffset ℓ height H P) m)
    (hD : P.1 ∈ FutureNoDrop ℓ n) (hE : P.2 ∈ FutureNoDrop ℓ m) :
    BoundaryAt ℓ (H : ℝ) P n m := by
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    have hh := hn.1
    rw [he] at hh
    omega
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have hh := hm.1
    rw [he] at hh
    omega
  refine ⟨hnpos,hmpos,⟨⟨firstLayerHit_record ℓ height hproj _ n P.1 hn,hD⟩,
    ⟨firstLayerHit_record ℓ height hproj _ m P.2 hm,hE⟩,?_⟩,?_,?_⟩
  · rw [hproj,hproj,hn.1,hm.1]
  · rw [hproj,hn.1]
    exact_mod_cast (show H ≤ H+(commonOffset ℓ height H P : ℤ) by omega)
  · intro j k hj hjn hk hkm hjH hc
    have heq : height (P.1 j) = height (P.2 k) := by
      have he := hc.2.2
      rw [hproj,hproj] at he
      exact_mod_cast he
    have hHj : H ≤ height (P.1 j) := by
      rw [hproj] at hjH
      exact_mod_cast hjH
    have hcn : P ∈ CommonLayer ℓ height (H+(height (P.1 j)-H).toNat) := by
      have he : H+((height (P.1 j)-H).toNat : ℤ) = height (P.1 j) := by omega
      rw [he]
      exact ⟨j,k,trueRecord_firstLayerHit ℓ height hproj _ _ hc.1,
        by rw [heq]; exact trueRecord_firstLayerHit ℓ height hproj _ _ hc.2.1,
        hc.1.2,hc.2.1.2⟩
    have hmin := commonOffset_min ℓ height H P (height (P.1 j)-H).toNat hcn
    have hlt := hn.2 j hjn
    omega

lemma firstLayerHit_recordIndexPosition_translated {d : ℕ} (e : Direction d)
    (x : Lattice d) (X : Path d) (hx : X 0 = x)
    (hD : X ∈ NoDrop (realPosition (step e)) x)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f) {H n : ℕ} (hH : 0 < H)
    (hn : X ∈ FirstLayerHit (signedHeight e) (signedHeight e x+H) n) :
    recordIndexPosition (realPosition (step e)) H (fun j => X j-x) = X n-x := by
  have h0 : (fun j => X j-x) 0 = 0 := by simp [hx]
  have hD' : (fun j => X j-x) ∈ NoDrop (realPosition (step e)) 0 := by
    change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' NoDrop (realPosition (step e)) 0
    rw [noDrop_translation]
    simpa only [add_zero] using hD
  have hn' : ∀ j, ∃ f, X (j+1)-x = (X j-x)+step f := by
    intro j
    obtain ⟨f,hf⟩ := hnn j
    exact ⟨f,by rw [hf]; abel⟩
  have hh : (fun j => X j-x) ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · rw [signedHeight_sub,hn.1]
      omega
    · intro j hj
      rw [signedHeight_sub]
      have := hn.2 j hj
      omega
  unfold recordIndexPosition
  rw [firstLayerHit_recordIndexTime e _ h0 hD' hn' hH hh]

lemma boundaryTimes_firstHit_identity {d : ℕ} (e f : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : RegularPath (realPosition (step e)) x P.1 ∧ P.1 ∈ NoDrop (realPosition (step e)) x)
    (hy : RegularPath (realPosition (step e)) y P.2 ∧ P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k)) :
    let ℓ := realPosition (step e)
    let J := H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    let nm := boundaryTimes ℓ ((signedHeight e x+H : ℤ) : ℝ) P
    signedCoordinate f (P.1 nm.1-P.2 nm.2) = physicalFirstHitGap ℓ f x y J P := by
  dsimp only
  let ℓ := realPosition (step e)
  let K := commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
  obtain ⟨n,m,hn,hm,hD,hE⟩ := commonOffset_spec ℓ (signedHeight e) (signedHeight e x+H) P hc
  have hb := firstCommonLayer_boundaryAt ℓ (signedHeight e) (signedHeight_projection e)
    (signedHeight e x+H) P (by rw [hx.1.1]; omega) (by rw [hy.1.1,← hxy]; omega)
    n m hn hm hD hE
  rw [boundaryTimes_eq ℓ _ P hb]
  have hn' : P.1 ∈ FirstLayerHit (signedHeight e) (signedHeight e x+(H+K)) n := by
    simpa only [Nat.cast_add,add_assoc] using hn
  have hm' : P.2 ∈ FirstLayerHit (signedHeight e) (signedHeight e y+(H+K)) m := by
    simpa only [← hxy,Nat.cast_add,add_assoc] using hm
  have h1 := firstLayerHit_recordIndexPosition_translated e x P.1 hx.1.1 hx.2 hx.1.2.1
    (show 0 < H+K by omega) hn'
  have h2 := firstLayerHit_recordIndexPosition_translated e y P.2 hy.1.1 hy.2 hy.1.2.1
    (show 0 < H+K by omega) hm'
  change _ = signedCoordinate f (x-y)+
    (signedCoordinate f (recordIndexPosition ℓ (H+K) (fun j => P.1 j-x))-
      signedCoordinate f (recordIndexPosition ℓ (H+K) (fun j => P.2 j-y)))
  rw [h1,h2]
  simp only [signedCoordinate_sub]
  ring

end DirectionalTransience

end

end

end OAI
