import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PairTail04
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators commutatorElement
open _root_.Polynomial _root_.OAI.Polynomial
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
lemma compact_horizontal_representatives [IsTopologicalGroup G]
    {n d : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z) :
    ∃ C : Set G, IsCompact C ∧ (∀ g : G, ∃ a∈C, a⁻¹*g∈Γ) ∧
      ∀ a∈C, ‖horizontal c hd a‖ ≤ 1 := by
  let B : Set (Fin n→ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  refine ⟨c.coord.symm '' B,hB.image c.coord.symm.continuous,?_,?_⟩
  · intro g
    refine ⟨reduceCoordinates c g n,⟨c.coord (reduceCoordinates c g n),?_,c.coord.symm_apply_apply _⟩,
      reduceCoordinates_coset c Γ hΓ g n⟩
    intro i _
    exact ⟨(reduceCoordinates_bounds c g n i i.isLt).1,(reduceCoordinates_bounds c g n i i.isLt).2.le⟩
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := ha
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    change |c.coord (c.coord.symm x) (Fin.castLE hd i)| ≤ 1
    rw [c.coord.apply_symm_apply]
    have hi := hx (Fin.castLE hd i) (Set.mem_univ _)
    exact (abs_of_nonneg hi.1).trans_le hi.2

lemma square_shift_scales (δ : ℝ) (hδ : 0<δ) :
    ∃ k : ℕ, 0<k ∧ ∀ N : ℕ, 2*k ≤ N →
      0<N/k ∧ N/k ≤ N ∧ (N:ℝ)/(2*k) ≤ (N/k:ℕ) ∧ 4*((N/k:ℕ):ℝ)/N ≤ δ^2/4 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (16/δ^2+1)
  have hkR : 0<(k:ℝ) := by
    have hh : 0 ≤ 16/δ^2 := div_nonneg (by norm_num) (sq_nonneg δ)
    linarith
  have hk0 : 0<k := by exact_mod_cast hkR
  refine ⟨k,hk0,?_⟩
  intro N hN
  have hN0 : 0<N := by omega
  have hNpos : 0<(N:ℝ) := by exact_mod_cast hN0
  have hmul : (N/k:ℕ)*k ≤ N := Nat.div_mul_le_self N k
  have hrem := Nat.mod_lt N hk0
  have hadd := Nat.mod_add_div N k
  rw [Nat.mul_comm k (N/k)] at hadd
  have hNR : 2*(k:ℝ) ≤ N := by exact_mod_cast hN
  have hupper : ((N/k:ℕ):ℝ)*(k:ℝ)  ≤  N := by exact_mod_cast hmul
  have hlower : (N:ℝ) < ((N/k:ℕ):ℝ)*(k:ℝ)+k := by
    have ht : N<(N/k)*k+k := by omega
    exact_mod_cast ht
  refine ⟨Nat.div_pos (by omega) hk0,Nat.div_le_self _ _,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0<(2:ℝ)*k)).mpr
    nlinarith
  · have hkd : 16  ≤  (k:ℝ)*δ^2 := by
      have hlt : 16/δ^2 <(k:ℝ) := by linarith
      have he := (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hlt
      linarith
    apply (div_le_iff₀ hNpos).mpr
    have hb := mul_le_mul_of_nonneg_left hupper (sq_nonneg δ)
    have ha := mul_le_mul_of_nonneg_right hkd (show 0 ≤ ((N/k:ℕ):ℝ) by positivity)
    nlinarith

variable {n d r : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable [((restricted H h0).level 2).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level 2) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level 2)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

include hlin hlevel hΓ hskR hΓR h1 hs in
 

theorem quadratic_vertical_correlation (hcomm : H.level 2=_root_.commutator G)
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      ‖horizontal c hd (f 1)‖ ≤ 1 → δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  obtain ⟨C,hCc,hC,hCb⟩ := compact_horizontal_representatives c hd Γ hΓ
  obtain ⟨Ξ,hΞ,B,hB,ρ,hρ,hprod⟩ := quadratic_square_characters H h0 h1 hs Γ cR hskR hΓR
    F hF χ hχ hw z hz hχz C hCc hC δ hδ
  obtain ⟨k,hk,hscale⟩ := square_shift_scales δ hδ
  have hden : 0<(2:ℝ)*k := by positivity
  obtain ⟨U,A,hA,N₀,hN₀,hdesc⟩ := uniform_character_of_commutator_level c hd hlin H h0 h1 hlevel Γ hΓ hcomm
    2 (by decide) hs Ξ (fun ξ h => (hΞ ξ h).1) (fun ξ h => (hΞ ξ h).2)
    (ρ/(2*k)) B (div_pos hρ hden) hB.le
  refine ⟨U,A,hA,max N₀ (2*k),lt_of_lt_of_le hN₀ (le_max_left _ _),?_⟩
  intro N hNN f hf hf0 hf1 hmean
  have hNN₀ := (le_max_left N₀ (2*k)).trans hNN
  have hNk := (le_max_right N₀ (2*k)).trans hNN
  obtain ⟨hT,hTN,hTd,hbound⟩ := hscale N hNk
  have hN : 0<N := hN₀.trans_le hNN₀
  obtain ⟨S,hST,hS,ξ,hξ,hξ0,hdata⟩ := hprod f hf hf0 N (N/k) hN hT hmean hbound
  choose v hv γ hγ hfac W hW hWe hWc using hdata
  let v' : ℕ→G := fun h => if hh : h∈S then v h hh else reduceCoordinates c (f 1^h) n
  have hv' (h : ℕ) : ‖horizontal c hd (v' h)‖ ≤ 1 := by
    dsimp [v']; split_ifs with hh
    · exact hCb _ (hv h hh)
    · exact reduced_horizontal_bound c hd _
  have hvΓ' (h : ℕ) : (v' h)⁻¹*f 1^h∈Γ := by
    dsimp [v']; split_ifs with hh
    · have he : f 1^h=v h hh*γ h hh := by simpa only [zpow_natCast] using hfac h hh
      rw [he,inv_mul_cancel_left]
      exact hγ h hh
    · exact reduceCoordinates_coset c Γ hΓ _ n
  apply hdesc N hNN₀ ξ hξ hξ0 f hf hf0 hf1 v' hv' hvΓ' S
  · intro h hh
    exact Finset.mem_range.mpr ((hST h hh).trans_le hTN)
  · calc
      ρ/(2*k)*(N:ℝ) = ρ*((N:ℝ)/(2*k)) := by ring
      _  ≤  ρ*((N/k:ℕ):ℝ) := mul_le_mul_of_nonneg_left hTd hρ.le
      _  ≤  _ := hS
  · intro h hh
    refine ⟨W h hh,?_,fun j hj _ => hWc h hh j hj⟩
    simpa only [v',dite_eq_left hh] using hWe h hh

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma integer_linear_return [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ℤ→G) (γ : G) (ξ : G→*Multiplicative ℝ)
    (a : ℤ) (ha : (ξ γ).toAdd=(a:ℝ)) (P : ℝ[X]) (hP : P.natDegree ≤ 2)
    (hPe : ∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z*(γ^z)⁻¹)).toAdd)
    (A : ℝ) (N : ℕ)
    (hPc : ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) :
    ∃ Q : ℝ[X], Q.natDegree ≤ 2 ∧ (∀ z : ℤ, Q.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |Q.coeff j-z| ≤ A/(N:ℝ)^j := by
  refine ⟨P+C (a:ℝ)*X,?_,?_,?_⟩
  · exact natDegree_add_le_of_degree_le hP ((natDegree_C_mul_le _ _).trans (by simp))
  · intro z
    simp only [eval_add,eval_mul,eval_C,eval_X,hPe,map_mul,map_inv,map_zpow,
      toAdd_mul,toAdd_inv,toAdd_zpow,
      zsmul_eq_mul,ha]
    ring
  · intro j hj
    obtain ⟨z,hz⟩ := hPc j hj
    by_cases he : j=1
    · subst j
      refine ⟨z+a,?_⟩
      simpa only [coeff_add,coeff_C_mul,coeff_X_one,mul_one,Int.cast_add,add_sub_add_right_eq_sub] using hz
    · refine ⟨z,?_⟩
      simpa [coeff_add,coeff_C_mul,coeff_X,he,Ne.symm he] using hz

variable {n d r : ℕ} (c : RealCoordinates G n) (hd : d ≤ n)
variable (hlin : ∀ i : Fin d, c.correction (Fin.castLE hd i)=0)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥)
variable [((restricted H h0).level 2).Normal]
variable (hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal c hd g=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable (cR : RealCoordinates ((level H h0 1)⧸(restricted H h0).level 2) r)
variable (hskR : SecondKind cR)
variable (hΓR : ∀ g, g∈((Γ.prod Γ).comap (level H h0 1).subtype).map
    (QuotientGroup.mk' ((restricted H h0).level 2)) ↔ ∀ i, ∃ z : ℤ, cR.coord g i=z)

include hlin hlevel hΓ hskR hΓR h1 hs in
 

theorem quadratic_vertical_correlation_unbounded_linear (hcomm : H.level 2=_root_.commutator G)
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (f : ℤ→G), LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  obtain ⟨U,A,hA,N₀,hN₀,hdesc⟩ := quadratic_vertical_correlation c hd hlin H h0 h1 hs hlevel Γ hΓ
    cR hskR hΓR hcomm F hF χ hχ hw z hz hχz δ hδ
  refine ⟨U,A,hA,N₀,hN₀,?_⟩
  intro N hNN f hf hf0 hmean
  let v := reduceCoordinates c (f 1) n
  let γ := v⁻¹*f 1
  have hγ : γ∈Γ := reduceCoordinates_coset c Γ hΓ (f 1) n
  have he : f 1=v*γ := by dsimp [γ]; group
  obtain ⟨hg,hg0,hg1,hge⟩ := lattice_linear_normalization H h1 Γ hf hf0 v γ hγ he
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hdesc N hNN (fun n => f n*(γ^n)⁻¹)
    hg hg0 (by
      change ‖horizontal c hd ((fun n : ℤ => f n*(γ^n)⁻¹) 1)‖ ≤ 1
      rw [hg1]; exact reduced_horizontal_bound c hd _) (by simpa only [hge] using hmean)
  obtain ⟨a,ha⟩ := hξΓ γ hγ
  exact ⟨ξ,hξ,hξ0,hξc,hξΓ,integer_linear_return f γ ξ a ha P hP hPe A N hPc⟩

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl UniformSquareObservable AbelianMalcevTorus MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥) (hcomm : H.level 2=_root_.commutator G)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hsk h0 h1 hs hcomm hqbound hq2 hq hΓ in
 

theorem quadratic_source_vertical_correlation
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (χ : G→ℂ)
    (hχ : ∀ n∈H.level 2, ‖χ n‖=1)
    (hw : ∀ n∈H.level 2, ∀ x : G, F (QuotientGroup.mk (x*n))=χ n*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level 2) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
      δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖ →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  have hH : ∀ g∈H.level 2, ∀ i : Fin (t+d), i.val<t → c.coord g i=0 := by
    intro g hg i hi
    exact (hq 2 g).mp hg i (by simpa only [hq2] using hi)
  let cH := horizontalCoordinates c hsk (H.level 2) t hcomm.ge hH
  have hlin : ∀ i : Fin t, cH.correction (i.castLE (Nat.le_add_right t d))=0 := by
    intro i
    exact horizontalCoordinates_correction c hsk (H.level 2) t hcomm.ge hH _ i.isLt
  have hlevel : ∀ g : G, g∈H.level 2 ↔ horizontal cH (Nat.le_add_right t d) g=0 := by
    intro g
    rw [hq 2,hq2]
    constructor
    · intro hg
      funext i
      exact hg (i.castLE (Nat.le_add_right t d)) i.isLt
    · intro hg i hi
      exact congrFun hg (⟨i.val,hi⟩ : Fin t)
  let := last_normal H h0 (by decide : 1 ≤ 2) hs
  let := PairTail.diagonal_normal (H.level 2) (H.level 2) (last_central_ambient H h1 2 hs)
  obtain ⟨cR,hskR,hΓR,_⟩ := exists_adapted_sourceReducedCoordinates H h0 h1 2 (by decide) hs
    c q hqbound hq2 hq Γ hΓ
  exact quadratic_vertical_correlation_unbounded_linear cH (Nat.le_add_right t d) hlin H h0 h1 hs hlevel
    Γ hΓ cR hskR hΓR hcomm F hF χ hχ hw z hz hχz δ hδ

end SquareInduction

end
end
end
end
end

end OAI
