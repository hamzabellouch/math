import OAI.Analysis.MarkovType.SubdivisionOperators

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

def extendPlacement {m : ℕ} (ι : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then ι ⟨i, h⟩ else Finset.univ.sup ι + 1 + (i - m)

@[simp] theorem extendPlacement_apply {m : ℕ} (ι : Fin m → ℕ) (i : Fin m) :
    extendPlacement ι i.val = ι i := by
  simp only [extendPlacement, dite_eq_left i.isLt]

theorem strictMono_extendPlacement {m : ℕ} (ι : Fin m → ℕ)
    (hι : StrictMono ι) : StrictMono (extendPlacement ι) := by
  classical
  intro i j hij
  simp only [extendPlacement]
  split_ifs with hi hj
  · exact hι (show (⟨i, hi⟩ : Fin m) < ⟨j, hj⟩ from hij)
  · have hb : ι ⟨i, hi⟩ ≤ Finset.univ.sup ι :=
      Finset.le_sup (Finset.mem_univ (⟨i, hi⟩ : Fin m))
    omega
  · omega
  · omega

theorem mapDomain_ofArray (f : ℕ → ℕ) {m : ℕ} (a : Fin m → ℝ) :
    Finsupp.mapDomain f (C00.ofArray a) = C00.place (fun i => f i.val) a := by
  classical
  simp only [C00.ofArray, C00.place, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single]

theorem mapDomain_extendPlacement {m : ℕ} (ι : Fin m → ℕ) (a : Fin m → ℝ) :
    Finsupp.mapDomain (extendPlacement ι) (C00.ofArray a) = C00.place ι a := by
  rw [mapDomain_ofArray]
  simp only [extendPlacement_apply]

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread in
theorem norm_mapDomain (f : ℕ → ℕ) (hf : StrictMono f) (x : C00) :
    p (Finsupp.mapDomain f x) = p x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha, mapDomain_ofArray]
  apply hspread
  intro i j hij
  exact hf (show i.val < j.val from hij)

include hspread in

theorem uniform_spreading (q : ℕ) (hq : 0 < q) {m : ℕ}
    (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    p (C00.uniformSubdivision q (C00.place ι a)) =
      p (C00.uniformSubdivision q (C00.ofArray a)) := by
  rw [← mapDomain_extendPlacement ι a, C00.uniformSubdivision_mapDomain q hq]
  exact norm_mapDomain p hspread _
    (C00.uniformBlockLift_strictMono q (extendPlacement ι) hq
      (strictMono_extendPlacement ι hι)) _

end MarkovSuperreflexivity.Subdivision

end

end OAI
