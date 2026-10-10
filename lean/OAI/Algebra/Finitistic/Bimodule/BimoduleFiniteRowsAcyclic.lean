import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalInsertion
import OAI.Algebra.Finitistic.Bimodule.BimoduleExactRows

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (hP : ∀ a, (∀ i, p i ≠ a) → IsZero (P.X a))
variable (hacyc : P.Acyclic) [∀ q, Projective (Z.X q)]

include hP in
omit [∀ q, Projective (Z.X q)] in
/-- A closed total element whose higher coordinates vanish is closed in the next row. -/
theorem closed_horizontal (n a : ℤ) (x : TotalTerm k B P p Z n)
    (hx : ((total k B P p hp Z).d n (n+1)).hom x = 0)
    (hhigh : coefficient k B P Z p n (a+1) x = 0) :
    horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl
      (coefficient k B P Z p n a x) = 0 := by
  have hc := congrArg (coefficient k B P Z p (n+1) (a+1)) hx
  erw [coefficient_d k B P Z p hp hP,hhigh,map_zero,zero_add,map_zero] at hc
  have transfer (b : ℤ) (hb : b=a) (hba : b+1=a+1) :
      horizontalBetween k B P Z n (n+1) b (a+1) rfl hba
        (coefficient k B P Z p n b x) =
      horizontalBetween k B P Z n (n+1) a (a+1) rfl rfl
        (coefficient k B P Z p n a x) := by
    subst b
    rfl
  rw [transfer (a+1-1) (by omega) (by omega)] at hc
  exact hc

include hP hacyc in
/-- Row-by-row elimination gives an actual preimage for every closed finite-total element. -/
theorem total_exact_of_rows (lo hi n : ℤ) (hlo : ∀ i, lo ≤ p i) (hhi : ∀ i, p i ≤ hi) :
    Function.Exact ((total k B P p hp Z).d (n-1) n).hom
      ((total k B P p hp Z).d n (n+1)).hom := by
  intro z
  constructor
  · intro hz
    let d := ((total k B P p hp Z).d (n-1) n).hom
    let e := ((total k B P p hp Z).d n (n+1)).hom
    have ed (w : TotalTerm k B P p Z (n-1)) : e (d w) = 0 :=
      congrArg (fun f => f.hom w) ((total k B P p hp Z).d_comp_d (n-1) n (n+1))
    have step (j : ℕ) : ∃ w : TotalTerm k B P p Z (n-1),
        ∀ b : ℤ, hi+1-(j : ℤ) ≤ b → coefficient k B P Z p n b (z-d w) = 0 := by
      induction j with
      | zero =>
        refine ⟨0, ?_⟩
        intro b hb
        erw [map_zero,sub_zero,coefficient_outside k B P Z p n b (by
          intro i heq
          have := hhi i
          omega),LinearMap.zero_apply]
      | succ j ih =>
        obtain ⟨w,hw⟩ := ih
        let a : ℤ := hi-(j : ℤ)
        let x := z-d w
        have hx : e x = 0 := by
          dsimp [x]
          rw [map_sub,hz,ed,sub_self]
        have hxhigh : coefficient k B P Z p n (a+1) x = 0 := hw (a+1) (by dsimp [a]; omega)
        have hc := closed_horizontal k B P Z p hp hP n a x hx hxhigh
        obtain ⟨y,hy⟩ := (horizontal_exact k B P Z hacyc n a _).mp hc
        let v := insertion k B P Z p (n-1) (a-1) y
        have hv : coefficient k B P Z p n a (d v) = coefficient k B P Z p n a x := by
          exact (coefficient_d_insertion_next k B P Z p hp hP (n-1) n (by omega)
            (a-1) a (by omega) y).trans hy
        refine ⟨w+v, ?_⟩
        intro b hb
        have hba : a ≤ b := by dsimp [a] at *; omega
        have hr : coefficient k B P Z p n b (z-d (w+v)) =
            coefficient k B P Z p n b x - coefficient k B P Z p n b (d v) := by
          dsimp [x]
          erw [map_add,map_sub,map_sub,map_add]
          abel
        rw [hr]
        by_cases hbeq : b=a
        · subst b
          rw [hv,sub_self]
        · have hbgt : a < b := lt_of_le_of_ne hba (Ne.symm hbeq)
          have hx0 := hw b (by dsimp [a] at *; omega)
          have hv0 : coefficient k B P Z p n b (d v) = 0 :=
            coefficient_d_insertion_above k B P Z p hp hP (n-1) n (by omega) (a-1) b (by omega) y
          rw [hx0,hv0,sub_self]
    obtain ⟨w,hw⟩ := step ((hi-lo).toNat+1)
    refine ⟨w, ?_⟩
    funext i
    have hwi := hw (p i) (by have := hlo i; omega)
    erw [coefficient_at k B P Z p hp] at hwi
    exact (sub_eq_zero.mp hwi).symm
  · rintro ⟨w,rfl⟩
    exact congrArg (fun f => f.hom w) ((total k B P p hp Z).d_comp_d (n-1) n (n+1))

include hP hacyc in
/-- A bounded acyclic bimodule complex tensors to an acyclic finite total with
any complex of projective left modules. The full outside B-action is retained. -/
theorem total_acyclic_of_rows (lo hi : ℤ) (hlo : ∀ i, lo ≤ p i) (hhi : ∀ i, p i ≤ hi) :
    (total k B P p hp Z).Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp)).mpr
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (total_exact_of_rows k B P Z p hp hP hacyc lo hi n hlo hhi)
end LittleFinitistic.BimoduleTotal

end

end OAI
