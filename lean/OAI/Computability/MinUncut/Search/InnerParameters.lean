import Mathlib
import OAI.Computability.MinUncut.Estimates.Assembly

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox

structure InnerParameters (J : ℝ) where
  s : ℕ
  m : ℕ
  k : ℕ
  n : ℕ
  H : ℕ
  A₀ : ℕ
  γ : ℚ
  p : ℚ
  θ : ℚ
  hm : 2 ≤ m
  hn : k+2 ≤ n
  hk : 1 ≤ k
  hs : ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*(smoothingRho (sourceSigma J))^(2*t) ≤ 1/16
  hroom : sourceR J*m < (m-s).choose 2
  hH : 0 < H
  hA : 0 < A₀
  hγ : 0 < (γ:ℝ)
  hp : 0 < (p:ℝ)
  hp1 : (p:ℝ) < 1
  hθ : 0 < (θ:ℝ)
  hθ1 : (θ:ℝ) < 1
  hloc : (sourceSigma J)⁻¹*Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) <
    classTarget (sourceT J) m/10
  henergy : (sourceSigma J)⁻¹^2/(H:ℝ) < classTarget (sourceT J) m/10
  hclip : 2*((sourceSigma J)⁻¹^2)/(A₀:ℝ) < classTarget (sourceT J) m/10
  hcollision : 2*(A₀:ℝ)*((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10
  hfourth : Real.sqrt ((H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ))) < classTarget (sourceT J) m/10
  hatom : Real.sqrt ((sourceSigma J)⁻¹^2)*Real.sqrt
    (((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
      Real.sqrt ((θ:ℝ)^2+(m:ℝ)*(p:ℝ)*(n^m:ℕ)/(sourceSigma J)^2))/(γ:ℝ)) <
    classTarget (sourceT J) m/10

lemma exists_innerParameters {J : ℝ} (hJ : 1 ≤ J) : Nonempty (InnerParameters J) := by
  have hσ := sourceSigma_pos hJ
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos hJ
  obtain ⟨s,hs⟩ := exists_cutoff (smoothingRho_lt_one hσ.ne') (by norm_num : (0:ℝ) < 1/16)
  obtain ⟨m,hm,_,hroom⟩ := exists_dimension (sourceR J) s
  let e := classTarget (sourceT J) m/10
  have he : 0 < e := div_pos (classTarget_pos hT m) (by norm_num)
  obtain ⟨H,A₀,γ,hH,hA,hγ,_,henergy,hclip,hfourth⟩ :=
    exists_reciprocal_processing (E := (sourceSigma J)⁻¹^2) he
  have hAr : (0:ℝ) < A₀ := by exact_mod_cast hA
  obtain ⟨k,hk,hcollision⟩ := exists_box_scale m hAr he
  obtain ⟨n,hn,hloc⟩ := exists_ambient_scale s (sourceR J*m) k hσ he
  let C := (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)
  have hchoose : 0 < (Fintype.card (Point m n)+s).choose s := Nat.choose_pos (by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  let L := (m:ℝ)*(n^m:ℕ)/(sourceSigma J)^2
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨p,θ,hp,hp1,hθ,hθ1,hQ⟩ := exists_small_rational_atoms hL
    (show 0 < (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 by positivity)
  have hQ' : (θ:ℝ)^2+(m:ℝ)*(p:ℝ)*(n^m:ℕ)/(sourceSigma J)^2 <
      (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 := by
    convert hQ using 1
    dsimp [L]
    ring
  have hatom := nested_atom_lt hσ he hγ hC hQ'
  exact ⟨⟨s,m,k,n,H,A₀,γ,p,θ,hm,hn,hk,hs,hroom,hH,hA,hγ,hp,hp1,hθ,hθ1,
    hloc,henergy,hclip,hcollision,hfourth,hatom⟩⟩

theorem InnerParameters.decode {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (w : Ξ → ℝ) (hw : ∀ ξ, 0 ≤ w ξ) (hw1 : ∑ ξ, w ξ=1)
    (f : ∀ ξ, FoldedProof (A ξ))
    (h1 : (∑ ξ, w ξ*firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J*(10*sourceSigma J))
    (h2 : (∑ ξ, w ξ*secondError (m := P.m) (n := P.n) (f ξ)
      ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (∑ ξ, w ξ*thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ ∑ ξ, w ξ*atomProbability (m := P.m) (n := P.n) (f ξ)
      (sourceSigma J) (sourceEta J) (P.θ:ℝ) := by
  apply inner_atom_of_errors V A w hw hw1 f hJ P.hm (by have := P.hn; omega)
    (by have := P.hn; omega) P.hs P.hroom (by exact_mod_cast P.hH) P.hγ
    (by exact_mod_cast P.hA) P.hθ.le P.hloc P.henergy P.hclip P.hcollision P.hfourth P.hatom
    h1 h2 h3
end MinUncut.Inner

end
end

end OAI
